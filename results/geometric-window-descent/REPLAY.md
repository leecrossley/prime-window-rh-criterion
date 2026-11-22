# Replaying the geometric specialization

Run these commands from `results/geometric-window-descent`. The package includes the local Lean sources, Sanftenberg’s pinned principal-character sources and the audit scripts. The three inputs are Lean 4.33.1, its matching Mathlib checkout and the public compiled geometric proof. Python 3.9 or later and the standard library suffice for the replay script.

## Prepare the public inputs

Start with Git, Elan, curl and zstd. Set `inputs` to a directory with room for the upstream archive and its extraction. The compressed download is 28,638,044,751 bytes. The 165,070 compiled objects used in the recorded comparisons occupy about 90 GB uncompressed, with additional space needed for the rest of the archive, Mathlib and build output. The cache is Jack McCarthy’s published build. The original proof has its own independent verification. [Pinned cache](https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/tree/9036e64326acf4acfae159b96664e9708445c1d1) · [Original verification](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)

```sh
inputs="$PWD/replay-inputs"
mkdir -p "$inputs/archive"
git clone --filter=blob:none --no-checkout https://github.com/leanprover-community/mathlib4.git "$inputs/mathlib4"
git -C "$inputs/mathlib4" checkout --detach 0df444a360eaa60ab8c11dca51a86af692955474
(cd "$inputs/mathlib4" && lake exe cache get)
lean_bin=$(cd "$inputs/mathlib4" && dirname "$(elan which lean)")

cache_url=https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/resolve/9036e64326acf4acfae159b96664e9708445c1d1
curl --fail --location --retry 3 --continue-at - "$cache_url/oleans.tar.zst" -o "$inputs/oleans.tar.zst"
(cd "$inputs" && printf '%s  %s\n' \
  953bab5386a7849527a11960f80a2fab427c49c637d6e94cc75788dd8f40196b oleans.tar.zst | sha256sum -c -)
zstd -dc "$inputs/oleans.tar.zst" | tar -xf - -C "$inputs/archive"
archive="$inputs/archive/.lake/build/lib/lean"
```

On macOS use `shasum -a 256 -c -` in place of `sha256sum -c -`. The runner checks the compiler revision, the Mathlib source hashes and the hash of every directly imported archive object. Lean 4.33.1 takes a package from the first library directory containing its root. When supplying several `--archive` paths, keep each top-level package together. The direct hashes come from the publisher’s `olean-manifest.sha256`, whose SHA-256 is `fb3609ad73a17102e6e3e2346c5358a9c0957bcf5945442a7e5ffaa00c441ff5`. Checking the compressed archive before extraction also covers transitive inputs. [Mathlib revision](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) [Publisher’s manifest](https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/blob/9036e64326acf4acfae159b96664e9708445c1d1/olean-manifest.sha256) [Lean’s module lookup](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Util/Path.lean#L61-L65)

## Run a replay

`rank` replays six arithmetic modules and audits the nine-generator proof. `window` runs the kernel on the case-two automorphy, count and window modules, then checks the 390,211 declarations of `window_from_second_seed` before the tower input is supplied. `proof` replays ten modules through the closed RH theorem and audits its dependencies. `compare` runs the RH and window audits and adds the two reference proofs. Each run creates a fresh directory under `--work` for the compiled objects and audit reports.

```sh
sh ../../verify-collection.sh
python3 replay.py rank --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
python3 replay.py window --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
python3 replay.py proof --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
```

For all three endpoints in one run, use the following command. The final audit retains the full declaration lists and recomputes the recorded hashes, membership checks and differences.

```sh
python3 replay.py compare --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
```

To inspect the build order before downloading the archive, use `python3 replay.py proof --list`. The rank, window, proof and comparison targets contain 11, 37, 74 and 81 package modules respectively, including their audits. The runner checks the reference endpoints in separate Lean processes because they give different implementations of some declarations.

Lean elaborates from source with `--trust=0` and warnings as errors. The standalone `leanchecker` checks the named modules against their compiled imports. The audit separately follows proof terms and types, checks Mathlib’s literal RH statement and the axiom set, and rejects any other reachable theorem with that literal type. The rank audit also excludes RH itself, Ferrero–Washington and the earlier tower estimates from the arithmetic calculation. The repository’s standard manifest check verifies package checksums. [Audit implementation](lean/AuditSlopeGraph.lean) · [Root-specific checks](lean/AuditGeometricRH.lean) · [Recorded runs](VERIFICATION.md)

## Hosted replay

The collection’s Result manifests workflow accepts an optional `geometric_target` when started manually. Select `compare` to check all three closed endpoints and the conditional window. The Ubuntu runner verifies both downloads, mounts the object archive read-only and saves the transcript, declaration lists and comparison for 30 days. [Workflow](../../.github/workflows/result-manifests.yml) [Runner script](hosted-replay.sh)
