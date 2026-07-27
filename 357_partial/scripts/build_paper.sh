#!/usr/bin/env bash
set -euo pipefail

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
BUILD_DIR="${1:-$ROOT/build/paper}"
TEX="$ROOT/paper/Erdos357AdaptiveBoundPaper.tex"
PDF="$ROOT/paper/Erdos357AdaptiveBoundPaper.pdf"

if ! command -v latexmk >/dev/null 2>&1; then
  echo "build_paper.sh requires latexmk" >&2
  exit 1
fi

mkdir -p "$BUILD_DIR"
export SOURCE_DATE_EPOCH=1785067200
export FORCE_SOURCE_DATE=1

latexmk \
  -pdf \
  -interaction=nonstopmode \
  -halt-on-error \
  -file-line-error \
  -outdir="$BUILD_DIR" \
  "$TEX"

install -m 0644 "$BUILD_DIR/Erdos357AdaptiveBoundPaper.pdf" "$PDF"
echo "paper built: $PDF"
