#!/usr/bin/env python3

import argparse
import json
import re
import sys


def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def sort_vars(entries):
    def sort_key(entry):
        return (
            entry.get("space", ""),
            entry.get("name", ""),
            entry.get("offset", 0),
            entry.get("size", 0),
            canonical_json(entry.get("meta", {})),
        )

    return sorted(entries, key=sort_key)


def normalize_symbol_prefixes(text):
    text = re.sub(r"\bsym\._", "sym.", text)
    text = re.sub(r"\bdbg\._", "dbg.", text)
    return text


def normalize_param_widths(text):
    def repl(match):
        token = match.group(0)
        return "uintN_t" if token.startswith("u") else "intN_t"

    return re.sub(r"\bu?int(?:32|64)_t(?=\s+arg\d+\b)", repl, text)


def normalize_decompiler(text):
    lines = [line.rstrip() for line in text.rstrip("\n").splitlines()]
    if not lines:
        return "\n"
    lines[0] = normalize_param_widths(normalize_symbol_prefixes(lines[0]))
    return "\n".join(lines) + "\n"


def normalize_signature_value(value):
    if isinstance(value, dict):
        return {key: normalize_signature_value_for_key(key, subvalue) for key, subvalue in value.items()}
    if isinstance(value, list):
        return [normalize_signature_value(item) for item in value]
    return value


def normalize_json_noise(value, ram_base=None):
    if isinstance(value, dict):
        normalized = {key: normalize_json_noise(subvalue, ram_base=ram_base) for key, subvalue in value.items()}
        if set(normalized.keys()) == {"Custom"}:
            return {"Custom": "space"}
        space = normalized.get("space")
        offset = normalized.get("offset")
        if (
            ram_base is not None
            and isinstance(space, str)
            and space.lower() == "ram"
            and isinstance(offset, int)
            and offset >= ram_base
        ):
            normalized["offset"] = offset - ram_base
        return normalized
    if isinstance(value, list):
        return [normalize_json_noise(item, ram_base=ram_base) for item in value]
    return value


def normalize_signature_value_for_key(key, value):
    if isinstance(value, dict):
        return {subkey: normalize_signature_value_for_key(subkey, subvalue) for subkey, subvalue in value.items()}
    if isinstance(value, list):
        return [normalize_signature_value(item) for item in value]
    if isinstance(value, str):
        value = normalize_symbol_prefixes(value)
        if key == "signature":
            value = normalize_param_widths(value)
        return value
    return value


def main():
    parser = argparse.ArgumentParser(description="Normalize r2r snapshot output.")
    parser.add_argument("mode", choices=["json", "regs", "vars", "decompiler", "signature-json"])
    parser.add_argument("--ram-base", type=lambda value: int(value, 0))
    args = parser.parse_args()

    raw = sys.stdin.read()

    if args.mode == "decompiler":
        sys.stdout.write(normalize_decompiler(raw))
        return

    value = json.loads(raw)
    value = normalize_json_noise(value, ram_base=args.ram_base)

    if args.mode == "regs":
        if isinstance(value, dict):
            for key in ("read", "write"):
                if isinstance(value.get(key), list):
                    value[key] = sorted(value[key])
    elif args.mode == "vars":
        if isinstance(value, list):
            value = sort_vars(value)
    elif args.mode == "signature-json":
        value = normalize_signature_value(value)

    sys.stdout.write(canonical_json(value) + "\n")


if __name__ == "__main__":
    main()
