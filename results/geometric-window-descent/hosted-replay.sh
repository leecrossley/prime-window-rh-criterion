#!/usr/bin/env bash
set -euo pipefail

case ${1:-} in
  rank|window|proof|compare|mizusawa-units|mizusawa-rank|mizusawa) target=$1 ;;
  *) exit 2 ;;
esac
stage=${2:-}
source_stage=${3:-}
if [[ -n "$stage" && "$target" != compare ]]; then exit 2; fi
note=$(cd "$(dirname "$0")" && pwd)
inputs=$(mktemp -d "${RUNNER_TEMP:?}/geometric-inputs.XXXXXXXX")
evidence="$RUNNER_TEMP/geometric-evidence"
mkdir -p "$inputs/archive" "$evidence"
exec > >(tee "$evidence/replay.log") 2>&1
git -C "$note" rev-parse HEAD
cd "$inputs"

download() {
  curl --fail --location --silent --show-error --retry 4 --continue-at - --output "$2" "$1"
  printf '%s  %s\n' "$3" "$2" | sha256sum -c -
}

cache=https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/resolve/9036e64326acf4acfae159b96664e9708445c1d1
download "$cache/oleans.tar.zst?download=true" oleans.tar.zst 953bab5386a7849527a11960f80a2fab427c49c637d6e94cc75788dd8f40196b
if ! command -v mksquashfs >/dev/null; then
  sudo apt-get update -qq
  sudo apt-get install -y --no-install-recommends squashfs-tools
fi
# Dropping the editor indexes leaves more space for swap. Lean reads the compiled objects from the compressed mount.
zstd -dc oleans.tar.zst \
  | tar --wildcards --wildcards-match-slash --delete -f - -- '*.ilean' \
  | mksquashfs - archive.sqfs -tar -no-strip -no-progress -noappend -no-xattrs -comp zstd -Xcompression-level 8 -mem 512M
sudo mount -o loop,ro,nosuid,nodev,noexec -t squashfs archive.sqfs archive
test -d archive/.lake/build/lib/lean/Formalism
rm oleans.tar.zst

download https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst lean.tar.zst 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235
tar --zstd -xf lean.tar.zst
rm lean.tar.zst
lean_bin="$inputs/lean-4.33.1-linux/bin"
export PATH="$lean_bin:$PATH"
git init -q mathlib4
git -C mathlib4 fetch --quiet --depth 1 https://github.com/leanprover-community/mathlib4.git 0df444a360eaa60ab8c11dca51a86af692955474
git -C mathlib4 checkout --quiet --detach FETCH_HEAD
(cd mathlib4 && lake exe cache get)
if [[ "$target" != rank && "$target" != mizusawa-rank && "$target" != mizusawa-units ]]; then
  sudo fallocate -l 40G extra.swap
  sudo chmod 600 extra.swap
  sudo mkswap extra.swap
  sudo swapon extra.swap
fi
df -h .
free -h

options=()
if [[ -n "$stage" ]]; then
  mkdir "$inputs/objects"
  if [[ -n "$source_stage" ]]; then
    checkpoint="$RUNNER_TEMP/geometric-checkpoint"
    test "$(cat "$checkpoint/revision")" = "$GITHUB_RUN_ID $GITHUB_SHA $source_stage"
    (cd "$checkpoint" && sha256sum -c objects.sha256)
    tar --zstd -xf "$checkpoint/objects.tar.zst" -C "$inputs/objects"
  fi
  options=(--stage "$stage" --stage-objects "$inputs/objects")
fi
python3 -Bu "$note/replay.py" "$target" --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$inputs/archive/.lake/build/lib/lean" --work "$inputs/runs" "${options[@]}"
if [[ "$stage" == common || "$stage" == build-* ]]; then
  saved="$RUNNER_TEMP/geometric-saved"
  mkdir "$saved"
  tar --zstd -cf "$saved/objects.tar.zst" -C "$inputs/objects" .
  (cd "$saved" && sha256sum objects.tar.zst > objects.sha256)
  printf '%s %s %s\n' "$GITHUB_RUN_ID" "$GITHUB_SHA" "$stage" > "$saved/revision"
fi
shopt -s nullglob
for run in "$inputs/runs"/*; do
  for list in "$run"/*-names.txt; do
    gzip -c "$list" > "$evidence/$(basename "$list").gz"
  done
  if [[ -d "$run/comparison" ]]; then
    cp -r "$run/comparison" "$evidence/"
  fi
done
