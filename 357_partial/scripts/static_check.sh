#!/usr/bin/env bash
set -euo pipefail

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
LEAN_FILE="$ROOT/Erdos357AdaptiveBound.lean"

if [[ ! -f "$LEAN_FILE" ]]; then
  echo "missing Lean source: $LEAN_FILE" >&2
  exit 1
fi

if ! command -v rg >/dev/null 2>&1; then
  echo "static_check.sh requires ripgrep (rg)" >&2
  exit 1
fi

forbidden='^[[:space:]]*(axiom|unsafe)[[:space:]]|^[[:space:]]*(sorry|admit)\b|(:=|=>|by|exact)[[:space:]]*(sorry|admit)\b'
if rg -n --pcre2 "$forbidden" "$LEAN_FILE"; then
  echo "forbidden Lean declaration or proof placeholder found" >&2
  exit 1
fi

if rg -n $'\r' "$LEAN_FILE"; then
  echo "CRLF or stray carriage return found in Lean source" >&2
  exit 1
fi

line_count="$(wc -l < "$LEAN_FILE" | tr -d ' ')"
digest="$(sha256sum "$LEAN_FILE" | awk '{print $1}')"

echo "static Lean audit: PASS"
echo "source lines: $line_count"
echo "source SHA-256: $digest"
