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

On macOS use `shasum -a 256 -c -` in place of `sha256sum -c -`. An existing extraction of the verified archive and an existing build of the pinned Mathlib can be used directly. The runner checks the compiler revision, Mathlib source hashes and the directly imported archive object hashes. The latter come from the publisher’s `olean-manifest.sha256`, whose SHA-256 is `fb3609ad73a17102e6e3e2346c5358a9c0957bcf5945442a7e5ffaa00c441ff5`. Authenticating the compressed archive above covers the transitive inputs. [Mathlib revision](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) · [Publisher’s manifest](https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/blob/9036e64326acf4acfae159b96664e9708445c1d1/olean-manifest.sha256)

## Run a replay

`rank` builds the two generator bounds, replays their arithmetic in the standalone kernel and audits the nine-generator proof independently of RH. `proof` builds the specialized geometric endpoint, replays the ten named mathematical modules including the final theorem, then checks its dependencies. `compare` additionally builds and audits the two reference endpoints and reproduces the comparison table. Each run creates its own directory under `--work`. The printed timestamps and outputs can be kept as a verification record.

```sh
sh ../../verify-collection.sh
python3 replay.py rank --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
python3 replay.py proof --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
```

For all three endpoints in one run, use the following command. The final audit retains the full declaration lists and recomputes the recorded hashes, membership checks and differences.

```sh
python3 replay.py compare --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
```

To replay the conditional window before applying the nine-generator bound, run the following command. It builds 37 modules including the audit. The runner resolves each direct import against the configured archive and package search paths. Every imported archive object must have a matching SHA-256 entry.

```sh
python3 replay.py window --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
```

For the three-generator proof from unit signs, use `real-unit-rows` for the Mathlib calculation and `tame-eight` for the arithmetic tower bound. [Commands and receipts](mizusawa/tame-signs/README.md#replay)

To inspect the source order before downloading the archive, run `python3 replay.py proof --list`. The full proof has 74 package modules including its audit. The standalone rank replay has 11. The baseline and the specialization give different implementations of some declarations, so the runner checks their endpoints in separate Lean processes.

Lean elaborates from source with `--trust=0` and warnings as errors. The standalone `leanchecker` checks the named modules against their compiled imports. The audit separately follows proof terms and types, checks Mathlib’s literal RH statement and the axiom set, and rejects any other reachable theorem with that literal type. The rank audit also excludes RH itself, Ferrero–Washington and the earlier tower estimates from the arithmetic calculation. The repository’s standard manifest check verifies package checksums. [Audit implementation](lean/AuditSlopeGraph.lean) · [Root-specific checks](lean/AuditGeometricRH.lean) · [Recorded runs](VERIFICATION.md)
