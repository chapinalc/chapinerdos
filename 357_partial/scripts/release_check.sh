#!/usr/bin/env bash
set -euo pipefail

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
cd "$ROOT"

required=(
  "Erdos357AdaptiveBound.lean"
  "lakefile.lean"
  "lake-manifest.json"
  "lean-toolchain"
  "paper/Erdos357AdaptiveBoundPaper.tex"
  "CITATION.cff"
  ".zenodo.json"
)

for path in "${required[@]}"; do
  if [[ ! -f "$path" ]]; then
    echo "required release file is missing: $path" >&2
    exit 1
  fi
done

placeholder_pattern='REPLACE_ME|REPLACE BEFORE RELEASE|AUTHOR NAME|AFFILIATION'
if rg -n "$placeholder_pattern" \
    README.md CITATION.cff .zenodo.json paper; then
  echo "release metadata still contains placeholders" >&2
  exit 1
fi

./scripts/static_check.sh

if ! command -v lake >/dev/null 2>&1; then
  echo "release_check.sh requires Lake/Lean" >&2
  exit 1
fi

lake build
./scripts/build_paper.sh

if command -v pdfinfo >/dev/null 2>&1; then
  pages="$(pdfinfo paper/Erdos357AdaptiveBoundPaper.pdf | awk '/^Pages:/ {print $2}')"
  if [[ -z "$pages" || "$pages" -lt 1 ]]; then
    echo "paper PDF has no readable pages" >&2
    exit 1
  fi
fi

if [[ -d .git ]]; then
  git diff --check
fi

echo "release checks: PASS"
