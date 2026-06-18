//! Syntax highlighting for rendered C text.
//!
//! This is intentionally a post-render presentation pass. The decompiler and
//! engine caches continue to carry plain C; terminal callers can opt into ANSI
//! highlighting at the final display boundary.

const RESET: &str = "\x1b[0m";
const COMMENT: &str = "\x1b[90m";
const STRING: &str = "\x1b[93m";
const NUMBER: &str = "\x1b[94m";
const KEYWORD: &str = "\x1b[95m";
const TYPE: &str = "\x1b[96m";
const FUNCTION: &str = "\x1b[1m";
const PREPROCESSOR: &str = "\x1b[92m";

/// Highlight rendered C source using ANSI escape sequences.
///
/// The tokenizer is deliberately shallow: it recognizes comments, strings,
/// character literals, numeric literals, C keywords, C-ish type names, and
/// function identifiers. It never changes text content or layout.
pub fn highlight_c_ansi(source: &str) -> String {
    let mut out = String::with_capacity(source.len() + source.len() / 4);
    let bytes = source.as_bytes();
    let mut i = 0usize;
    let mut line_start = true;

    while i < bytes.len() {
        let b = bytes[i];

        if !b.is_ascii() {
            let ch = source[i..].chars().next().expect("valid utf-8 boundary");
            out.push(ch);
            line_start = ch == '\n';
            i += ch.len_utf8();
            continue;
        }

        if line_start && (b == b' ' || b == b'\t') {
            out.push(b as char);
            i += 1;
            continue;
        }

        if line_start && b == b'#' {
            let end = scan_line(bytes, i);
            push_styled(&mut out, PREPROCESSOR, &source[i..end]);
            line_start = end < bytes.len() && bytes[end] == b'\n';
            i = end;
            continue;
        }

        if b == b'/' && bytes.get(i + 1) == Some(&b'/') {
            let end = scan_line(bytes, i);
            push_styled(&mut out, COMMENT, &source[i..end]);
            line_start = end < bytes.len() && bytes[end] == b'\n';
            i = end;
            continue;
        }

        if b == b'/' && bytes.get(i + 1) == Some(&b'*') {
            let end = scan_block_comment(bytes, i);
            push_styled(&mut out, COMMENT, &source[i..end]);
            line_start = source[i..end].ends_with('\n');
            i = end;
            continue;
        }

        if b == b'"' || b == b'\'' {
            let end = scan_quoted(bytes, i, b);
            push_styled(&mut out, STRING, &source[i..end]);
            line_start = false;
            i = end;
            continue;
        }

        if b.is_ascii_digit() {
            let end = scan_number(bytes, i);
            push_styled(&mut out, NUMBER, &source[i..end]);
            line_start = false;
            i = end;
            continue;
        }

        if is_ident_start(b) {
            let end = scan_ident(bytes, i);
            let ident = &source[i..end];
            let style = if is_c_keyword(ident) {
                Some(KEYWORD)
            } else if is_c_type_like(ident) {
                Some(TYPE)
            } else if is_function_ident(bytes, end) {
                Some(FUNCTION)
            } else {
                None
            };
            if let Some(style) = style {
                push_styled(&mut out, style, ident);
            } else {
                out.push_str(ident);
            }
            line_start = false;
            i = end;
            continue;
        }

        out.push(b as char);
        line_start = b == b'\n';
        i += 1;
    }

    out
}

fn push_styled(out: &mut String, style: &str, text: &str) {
    out.push_str(style);
    out.push_str(text);
    out.push_str(RESET);
}

fn scan_line(bytes: &[u8], mut i: usize) -> usize {
    while i < bytes.len() && bytes[i] != b'\n' {
        i += 1;
    }
    i
}

fn scan_block_comment(bytes: &[u8], mut i: usize) -> usize {
    i += 2;
    while i + 1 < bytes.len() {
        if bytes[i] == b'*' && bytes[i + 1] == b'/' {
            return i + 2;
        }
        i += 1;
    }
    bytes.len()
}

fn scan_quoted(bytes: &[u8], mut i: usize, quote: u8) -> usize {
    i += 1;
    while i < bytes.len() {
        if bytes[i] == b'\\' {
            i = (i + 2).min(bytes.len());
            continue;
        }
        if bytes[i] == quote {
            return i + 1;
        }
        i += 1;
    }
    bytes.len()
}

fn scan_number(bytes: &[u8], mut i: usize) -> usize {
    while i < bytes.len() {
        let b = bytes[i];
        if b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_') {
            i += 1;
        } else {
            break;
        }
    }
    i
}

fn scan_ident(bytes: &[u8], mut i: usize) -> usize {
    while i < bytes.len() && is_ident_continue(bytes[i]) {
        i += 1;
    }
    i
}

fn is_function_ident(bytes: &[u8], mut i: usize) -> bool {
    while i < bytes.len() && bytes[i].is_ascii_whitespace() {
        i += 1;
    }
    bytes.get(i) == Some(&b'(')
}

fn is_ident_start(b: u8) -> bool {
    b == b'_' || b.is_ascii_alphabetic()
}

fn is_ident_continue(b: u8) -> bool {
    is_ident_start(b) || b.is_ascii_digit()
}

fn is_c_keyword(ident: &str) -> bool {
    matches!(
        ident,
        "break"
            | "case"
            | "continue"
            | "default"
            | "do"
            | "else"
            | "for"
            | "goto"
            | "if"
            | "return"
            | "switch"
            | "while"
    )
}

fn is_c_type_like(ident: &str) -> bool {
    matches!(
        ident,
        "bool"
            | "char"
            | "const"
            | "double"
            | "enum"
            | "float"
            | "int"
            | "long"
            | "short"
            | "signed"
            | "size_t"
            | "ssize_t"
            | "struct"
            | "uint8_t"
            | "uint16_t"
            | "uint32_t"
            | "uint64_t"
            | "int8_t"
            | "int16_t"
            | "int32_t"
            | "int64_t"
            | "union"
            | "unsigned"
            | "void"
            | "volatile"
    ) || ident.ends_with("_t")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strip_ansi(input: &str) -> String {
        let bytes = input.as_bytes();
        let mut out = String::new();
        let mut i = 0usize;
        while i < bytes.len() {
            if bytes[i] == 0x1b {
                i += 1;
                if i < bytes.len() && bytes[i] == b'[' {
                    i += 1;
                    while i < bytes.len() && bytes[i] != b'm' {
                        i += 1;
                    }
                    if i < bytes.len() {
                        i += 1;
                    }
                }
            } else {
                out.push(bytes[i] as char);
                i += 1;
            }
        }
        out
    }

    #[test]
    fn ansi_highlight_preserves_source_text() {
        let source = "size_t count_bytes(uint8_t* buf, size_t n)\n{\n    return 0;\n}\n";
        let highlighted = highlight_c_ansi(source);

        assert_ne!(highlighted, source);
        assert_eq!(strip_ansi(&highlighted), source);
        assert!(highlighted.contains("\x1b[96msize_t\x1b[0m"));
        assert!(highlighted.contains("\x1b[1mcount_bytes\x1b[0m"));
        assert!(highlighted.contains("\x1b[95mreturn\x1b[0m"));
        assert!(highlighted.contains("\x1b[94m0\x1b[0m"));
    }

    #[test]
    fn ansi_highlight_does_not_tokenize_inside_comments_or_strings() {
        let source = "/* return 0 */\nchar* s = \"if return 123\";\n";
        let highlighted = highlight_c_ansi(source);

        assert_eq!(strip_ansi(&highlighted), source);
        assert!(highlighted.contains("\x1b[90m/* return 0 */\x1b[0m"));
        assert!(highlighted.contains("\x1b[93m\"if return 123\"\x1b[0m"));
        assert!(!highlighted.contains("\"\x1b[95mif\x1b[0m"));
    }
}
