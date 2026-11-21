#!/usr/bin/env bash
set -euo pipefail
repo=$(cd "$(dirname "$0")" && pwd)
cd "$repo"
if command -v sha256sum >/dev/null 2>&1; then
  sha256sum --check SHA256SUMS
else
  shasum -a 256 -c SHA256SUMS
fi
result=$(mktemp)
trap 'rm -f -- "$result"' EXIT
python3 verify.py > "$result"
diff -u evidence/check.txt "$result"
cat "$result"
