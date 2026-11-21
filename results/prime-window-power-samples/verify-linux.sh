#!/usr/bin/env bash
set -euo pipefail

if [[ "$(uname -s):$(uname -m)" != Linux:x86_64 ]]; then
  echo "Use the installed Mathlib instructions in README.md on this platform." >&2
  exit 2
fi
repo=$(cd "$(dirname "$0")" && pwd)
(cd "$repo" && sha256sum --check SHA256SUMS)
python3 "$repo/check_weight.py"
python3 "$repo/finite/check_quartic_exact.py"
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
cd "$scratch"

get_archive() {
  curl --fail --silent --show-error --location --retry 4 --output "$2" "$1"
  printf '%s  %s\n' "$3" "$2" | sha256sum --check -
}
get_archive https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst \
  lean.tar.zst 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235
tar --zstd -xf lean.tar.zst
export PATH="$scratch/lean-4.33.1-linux/bin:$PATH"

mathlib_revision=0df444a360eaa60ab8c11dca51a86af692955474
git init -q mathlib4
git -C mathlib4 remote add origin https://github.com/leanprover-community/mathlib4.git
git -C mathlib4 fetch --quiet --depth 1 origin "$mathlib_revision"
git -C mathlib4 checkout --quiet --detach FETCH_HEAD
test "$(git -C mathlib4 rev-parse HEAD)" = "$mathlib_revision"
get_archive https://github.com/CocoSgt/riemann-hypothesis-lean/releases/download/v2026-11-20/lean.tar.gz \
  upstream.tar.gz 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc
tar -xzf upstream.tar.gz

cd mathlib4
lake exe cache get
lake env sh "$repo/finite/replay_corners.sh"
lake env lean -DautoImplicit=false -R "$repo/pairs" -o "$scratch/PairSignChecks.olean" "$repo/pairs/PairSignChecks.lean"
lake env sh -c 'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; exec leanchecker -v PairSignChecks' sh "$scratch"
lake env python3 "$repo/verify.py" "$scratch/lean/src"
