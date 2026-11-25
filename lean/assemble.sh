#!/bin/sh
# Assemble the Lean project that was built and checked for this repository.
#
# Usage (from this folder, lean/):
#   git clone https://github.com/openai/math openai-math
#   git -C openai-math checkout 3344da59991ed94f9ba711217b29c1d760badfa6
#   sh assemble.sh openai-math
#
# What it does:
#   1. copies the 288 unchanged files of OpenAI's Lean library listed in oai_files.txt
#      (from <checkout>/lean/) into this folder and checks them against OAI-SHA256SUMS;
#   2. copies ../Challenge/Statement.lean to ComparatorChallenge/HadwigerScaled.lean
#      (the module name that was built) and checks our 5 files against OURS-SHA256SUMS.
# It does not download anything and does not build anything.
set -eu

COMMIT=3344da59991ed94f9ba711217b29c1d760badfa6

if [ $# -ne 1 ]; then
  echo "usage: sh assemble.sh <path to a checkout of github.com/openai/math at $COMMIT>" >&2
  exit 2
fi
REPO=$1
HERE=$(cd "$(dirname "$0")" && pwd)
cd "$HERE"

if command -v git >/dev/null 2>&1 && [ -d "$REPO/.git" ]; then
  HEAD=$(git -C "$REPO" rev-parse HEAD)
  if [ "$HEAD" != "$COMMIT" ]; then
    echo "error: $REPO is at $HEAD, expected $COMMIT" >&2
    exit 1
  fi
fi

if command -v sha256sum >/dev/null 2>&1; then
  SHA="sha256sum"
else
  SHA="shasum -a 256"
fi

while IFS= read -r f; do
  [ -n "$f" ] || continue
  mkdir -p "$(dirname "$f")"
  cp "$REPO/lean/$f" "$f"
done < oai_files.txt

mkdir -p ComparatorChallenge
cp ../Challenge/Statement.lean ComparatorChallenge/HadwigerScaled.lean

$SHA -c OAI-SHA256SUMS > /dev/null
$SHA -c OURS-SHA256SUMS > /dev/null
echo "OK: 288 OpenAI files and 5 files of this repository match OAI-SHA256SUMS and OURS-SHA256SUMS."
echo "Next (needs elan; the build used Lean 4.34.1 and Mathlib d13f23b, see lean-toolchain and lake-manifest.json):"
echo "  lake exe cache get"
echo "  ulimit -n 8192; LEAN_NUM_THREADS=4 lake build OAI.Combinatorics.HadwigerScaled.Main ComparatorChallenge.HadwigerScaled"
echo "  lake env lean Check/Axioms.lean"
echo "  lake env lean Check/ChallengeView.lean > chal.txt; lake env lean Check/SolutionView.lean > sol.txt; cmp chal.txt sol.txt"
