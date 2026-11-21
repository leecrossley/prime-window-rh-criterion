# Verification of the Möbius criterion, finite certificates and cutoff lemmas

| Result | Evidence |
| --- | --- |
| Equivalence of RH with either one-sided Möbius loss bound on arbitrarily late fourth-power blocks | Lean checks the signed excursions, rounding, arithmetic discrepancy and cofinal quantifiers. The dependency audit follows nine named theorem roots and rejects any previously closed theorem whose type is `RiemannHypothesis`. [Criterion](lean/FourthSignedCriterion.lean) · [Audit](lean/FourthSignedAudit.lean) |
| Both logarithmic budgets for $10^4\le m\le2\cdot10^6$ and the square-block deficit bound through $K=5.7\cdot10^{12}$ | Lean checks the arithmetic and the finite implications from the displayed envelope for $D$. The [finite proof](FINITE.md) supplies the envelope from published zero verification and the family’s explicit inequalities. Arb encloses the constants at two precisions. [Six-root audit](lean/FiniteQuarticAudit.lean) |
| Nonnegative terminal intervals, the full-grid criterion, local weighted means and the same-block comparison | The [signed-prefix proof](CUTOFFS.md) and [local averaging proof](LOCAL-AVERAGES.md) are written mathematics. Lean checks eight components covering the weight correction, normalization of the actual arithmetic means, the log-prefix derivative and the integral and width inequalities. The transfer to actual zeta zeros is in the written proofs. [Cutoff audit](lean/CutoffAudit.lean) |

The direct, fixed lower bound at every cutoff in $[Q/\log Q,Q]$ on arbitrarily late square blocks remains open.

## Replay the certificates

From this directory, using Python with `python-flint==0.9.0`, run

```sh
python3 -B check_finite_quartic.py
python3 -B check_cutoffs.py
```

The first script uses outward rounding at 160 and 256 bits. The last mass values below are upper estimates derived from the envelope. Lean proves coverage between the tested endpoints.

| Block parameter $m$ | Mass majorant, rounded up | Allowed $2(1+2\log m)$, rounded down |
| --- | ---: | ---: |
| 10,000 | 21.184013 | 38.841361 |
| 1,000,000 | 33.303455 | 57.262042 |
| 2,000,000 | 57.814359 | 60.034630 |

The second script uses rational arithmetic. It checks 187 points of the taper and a 41-node manufactured grid with two independent sample columns. One set of strictly positive weights gives exact zero mean for each column. Both columns have negative entries.

## Replay the Lean proofs

The Linux entry point runs both numerical checks with the pinned python-flint version, then obtains and checks the Lean release, Mathlib checkout and upstream analytic source archive. Run it from the perfect-power directory. The family workflow calls this script on changes to the perfect-power result. [Linux replay](../../verify-linux.sh) · [Family workflow](../../../../.github/workflows/prime-pair-bounds.yml)

```sh
bash verify-linux.sh
```

For the Möbius and cutoff proofs alone, use Lean **4.33.1** (commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474` and the upstream `src` at `40e56bab026552e089d7afcfeff08d2defb9c005`. From that Mathlib checkout, with its usual library cache installed, run

```sh
study=/absolute/path/to/prime-window-rh-criterion/results/prime-window-power-samples/pairs/mobius
upstream=/absolute/path/to/riemann-hypothesis/src
build=$(mktemp -d)
lake env python3 -B "$study/replay.py" "$upstream" "$build" --jobs 2
```

The replay follows the imports of the three audits. It checks all 311 upstream source hashes against the [family pins](../../evidence/upstream.sha256) and the [additional pins](upstream.sha256), builds those modules and the 65 project modules in the empty directory, and runs `leanchecker` on ten result modules. Thirteen project modules come directly from the existing perfect-power source directory. The finite and cutoff audits reject a dependency on the RH proposition. All three audits check the standard axiom set. [Mathlib revision](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) · [Upstream analytic sources](https://github.com/Deicyde/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005/src)

On 21 November 2026 a clean macOS arm64 run built all 376 modules with Lean 4.33.1. Each audit reported the following declarations reachable from its own statements.

| Audit | Statements | Reachable declarations |
| --- | ---: | ---: |
| Fourth-power criterion | 9 | 63,461 |
| Finite certificates | 6 | 43,246 |
| Cutoff lemmas | 8 | 39,555 |

After the audits, `leanchecker` replayed all ten result modules successfully.
