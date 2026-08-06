#!/usr/bin/env bash
set -euo pipefail

check_radare2() {
  [ -x "$RADARE2_CACHE_DIR/binr/radare2/radare2" ] &&
    command -v r2 >/dev/null &&
    command -v r2r >/dev/null &&
    pkg-config --exists r_anal &&
    "$RADARE2_CACHE_DIR/binr/radare2/radare2" -v >/dev/null 2>&1
}

RADARE2_REPO_URL="https://github.com/radareorg/radare2"
RADARE2_REF="master"

RADARE2_REMOTE_REF="$(git ls-remote "$RADARE2_REPO_URL" "refs/heads/$RADARE2_REF" | cut -f1)"
if [ -z "$RADARE2_REMOTE_REF" ]; then
  RADARE2_REMOTE_REF="$(git ls-remote "$RADARE2_REPO_URL" "$RADARE2_REF" | cut -f1 | head -n1)"
fi
if [ -z "$RADARE2_REMOTE_REF" ]; then
  echo "::error::Failed to resolve radare2 ref '$RADARE2_REF' from $RADARE2_REPO_URL"
  exit 1
fi

RADARE2_CACHE_KEY="$(printf '%s-%s' "$RADARE2_REPO_URL" "$RADARE2_REF" | tr -cs 'A-Za-z0-9._-' '-')"
RADARE2_CACHE_DIR="${R2SLEIGH_RADARE2_CACHE_DIR:-/tmp/radare2-$RADARE2_CACHE_KEY}"
RADARE2_INSTALL_REF_FILE="$RADARE2_CACHE_DIR/.r2sleigh-installed-ref"

RADARE2_CACHE_REF=""
RADARE2_INSTALLED_REF=""
if [ -d "$RADARE2_CACHE_DIR/.git" ]; then
  RADARE2_CACHE_REF="$(git -C "$RADARE2_CACHE_DIR" rev-parse HEAD 2>/dev/null || true)"
fi
if [ -f "$RADARE2_INSTALL_REF_FILE" ]; then
  RADARE2_INSTALLED_REF="$(cat "$RADARE2_INSTALL_REF_FILE")"
fi

NEED_RADARE2_INSTALL=0
if ! check_radare2; then
  echo "radare2/r2r/headers missing or unusable for $RADARE2_REPO_URL@$RADARE2_REF"
  NEED_RADARE2_INSTALL=1
fi
if [ "$RADARE2_CACHE_REF" != "$RADARE2_REMOTE_REF" ]; then
  echo "radare2 cache ref mismatch: cache=${RADARE2_CACHE_REF:-missing} remote=$RADARE2_REMOTE_REF"
  NEED_RADARE2_INSTALL=1
fi
if [ "$RADARE2_INSTALLED_REF" != "$RADARE2_REMOTE_REF" ]; then
  echo "radare2 installed ref mismatch: installed=${RADARE2_INSTALLED_REF:-missing} remote=$RADARE2_REMOTE_REF"
  NEED_RADARE2_INSTALL=1
fi

if [ "$NEED_RADARE2_INSTALL" -eq 0 ]; then
  echo "radare2 install already matches $RADARE2_REPO_URL@$RADARE2_REF ($RADARE2_REMOTE_REF)"
else
  echo "Refreshing radare2 from $RADARE2_REPO_URL@$RADARE2_REF..."
  rm -rf "$RADARE2_CACHE_DIR"
  git clone --depth=1 --branch "$RADARE2_REF" "$RADARE2_REPO_URL" "$RADARE2_CACHE_DIR"
  echo "Installed radare2 cache ref: $(git -C "$RADARE2_CACHE_DIR" rev-parse HEAD)"
  cd "$RADARE2_CACHE_DIR"
  sys/install.sh
  printf '%s\n' "$RADARE2_REMOTE_REF" > "$RADARE2_INSTALL_REF_FILE"
  cd "$GITHUB_WORKSPACE"
  check_radare2
fi

RADARE2_LD_LIBRARY_PATH="$(find "$RADARE2_CACHE_DIR/libr" -mindepth 1 -maxdepth 1 -type d 2>/dev/null | sort | paste -sd: -)"

{
  echo "LOCAL_R2_DIR=$RADARE2_CACHE_DIR"
  echo "R2R_RADARE2=$RADARE2_CACHE_DIR/binr/radare2/radare2"
  echo "R2SLEIGH_E2E_RADARE2=$RADARE2_CACHE_DIR/binr/radare2/radare2"
  echo "R2SLEIGH_CI_RADARE2_REF=$RADARE2_REMOTE_REF"
  if [ -n "$RADARE2_LD_LIBRARY_PATH" ]; then
    echo "LD_LIBRARY_PATH=$RADARE2_LD_LIBRARY_PATH${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
    echo "DYLD_LIBRARY_PATH=$RADARE2_LD_LIBRARY_PATH${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
  fi
} >> "$GITHUB_ENV"
