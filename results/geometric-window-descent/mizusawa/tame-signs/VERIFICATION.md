# Verification of the eight-character bound

## What Lean checks

The residue theorem holds for every primitive dyadic root of conductor at least 16 and every pair of primes in the indicated congruence classes. The arithmetic theorem bounds the continuous quadratic characters unramified away from those two primes on a finite cyclotomic layer. After quadratic descent it bounds the everywhere-unramified characters on the ordinary biquadratic tower. The identity of the host with the genus-field tower is available separately. [Statements](../../lean/CyclotomicEight.lean) · [Field identification](../../lean/MizusawaHostField.lean) · [Genus-field comparison](../../lean/MizusawaGenusField.lean)

| Audit root | Local sources, including the audit | Named modules replayed by `leanchecker` | Distinct reachable declarations |
| --- | ---: | ---: | ---: |
| `UnitSigns.row_counts` | 8 | 5 | 72,843 |
| `TameSigns.host_tower_three` | 27 | 14 | 100,303 |
| `ConductorOne.rh_from_tame_units` | 90 | 2 | 1,477,044 |

All three source builds started in an empty local build directory on 22 November 2026. Lean 4.33.1 elaborated the sources at `--trust=0` with warnings as errors. The rows use only the pinned Mathlib environment. The other targets also use the authenticated geometric archive. The two arithmetic transcripts include their full dependency audits. For the geometric endpoint, the build transcript records all 89 object modules and the standalone kernel replay. A separate audit exported the 1,477,044 reachable names. The public replay runs the build, kernel and audit together and verifies that name-set hash. Temporary replay directory names are replaced in the transcripts. [Rows transcript](evidence/rows-replay.txt) · [Tower transcript](evidence/tower-replay.txt) · [Geometric build and kernel](evidence/window-kernel.txt) · [Geometric audit](evidence/window-audit.txt) · [Input hashes](../../REPLAY.md) · [Publication and replay updates](https://github.com/leecrossley/prime-window-rh-criterion/pull/51)

The audit traverses the types and proof terms of the root theorem. It checks that only `propext`, `Classical.choice` and `Quot.sound` occur as axioms. The tower audit requires both the local Artin detection theorem and the absolute-to-finite inertia theorem. It rejects `sorryAx`, RH, the rank-three literature premise, the nine-generator result and Ferrero–Washington. Its new three-generator result therefore supplies an arithmetic input independently of RH. [Tower audit](../../lean/AuditTameEight.lean) · [Traversal](../../lean/AuditSlopeGraph.lean) · [Sorted dependency hashes](evidence/dependencies.json)

The geometric application has Mathlib’s literal type `RiemannHypothesis` with no premise. Its audit requires the tower theorem and the existing window argument, and rejects a dependency on any other theorem with that literal closed type. The archived argument still uses Ferrero–Washington elsewhere. The standalone sign and tower theorems can be used without that argument. The parameter `TowerBound` in `ordinary_three_input` converts the proved tower predicate into a cohomological estimate. The existing geometric argument supplies this estimate through `PropA.aBound_of_isTower`. [Geometric application](../../lean/TameEightWindowRH.lean) · [Endpoint audit](../../lean/AuditTameEightRH.lean) · [Use of the cohomological estimate](../../lean/SecondSeedWindow.lean)

## Effect on the geometric argument

| Closed theorem | Nine generators | Three from units | Added | Removed | Net change |
| --- | ---: | ---: | ---: | ---: | ---: |
| Ordinary tower bound | 77,321 | 100,303 | 23,122 | 140 | +22,982 |
| Full geometric RH theorem | 1,476,889 | 1,477,044 | 195 | 40 | +155 |

The interval selector now takes the proved witness $R=3$. At fixed $B=2C_K C_t/\varepsilon$, its window parameter changes from $2048B^9$ to $32B^3$ and its reference level changes from 6 to 4. The full geometric dependency set loses `ordinary_ray_six`, `host_rank_nine` and `ordinary_nine_input`. It gains the explicit unit and inertia arguments. In total there are 155 more reachable declarations in the full proof. The exact changes are available for the [tower additions](evidence/tower-added.txt.gz), [tower removals](evidence/tower-removed.txt.gz), [geometric additions](evidence/rh-added.txt.gz) and [geometric removals](evidence/rh-removed.txt.gz). [Selector calculation](../../lean/MizusawaSelector.lean) · [Closed comparisons](evidence/comparison.json) · [Previous nine-generator counts](../evidence/comparison.json)

To reproduce the differences, run the `rank`, `proof`, `tame-eight` and `tame-eight-rh` targets described in the replay guide. Set the four directory variables below to the fresh replay directories printed by the corresponding commands. Run this from `results/geometric-window-descent`. [Public replay](../../REPLAY.md) · [Comparison program](compare.py)

```sh
python3 mizusawa/tame-signs/compare.py \
  --nine-tower "$rank_dir/rank-names.txt" \
  --unit-tower "$eight_dir/tame-eight-names.txt" \
  --nine-rh "$proof_dir/second-rh-names.txt" \
  --unit-rh "$window_dir/tame-eight-rh-names.txt" \
  --differences "$inputs/runs/unit-differences"
```

## Independent residue calculation

The Python checker computes with polynomials in $\mathbb F_p[X]/(X^{2^{n-1}}+1)$. For each possible sign triple it uses Euler’s criterion and a polynomial gcd to count the irreducible factors giving that triple. It tests the primes in $(3,7)$, $(11,23)$ and $(547,727)$ at $n=4,5,6,7$, giving 24 prime/conductor combinations. At every $q$ both primes have three negative signs. At every $d$ two primes give each complementary pattern. For an outside case, at $n=4$ and $p=31$ all three elements are squares at all four primes. Frobenius sends $z$ to $z^{-1}$, so the two real units reduce to elements of $\mathbb F_{31}^{\times}$, all of which are squares in $\mathbb F_{31^2}$. A root of order 16 is also a square there because $32$ divides $31^2-1$. The uniform conclusion for the stated congruences comes from the Lean proof. [Program](check_residues.py) · [Exact output](evidence/residue-samples.txt)

## Prior work and scope

Mizusawa’s Lemma 4.2 gives the stronger arithmetic conclusion of freeness and rank three. The `bramble_trace` reading guide gives the same sign rows using the norm of the real unit and an automorphism of the residue pairs. It then applies Chevalley’s formula and the index-two Schreier bound. The formal proof here specifies the automorphism $z\mapsto z^3$, computes signs directly in the residue fields and transfers the three global Artin relations to the chosen tame generators in the geometric library. [Mizusawa, 2010](https://www.numdam.org/item/10.5802/jtnb.707.pdf#page=13) · [Reading guide, revision 29](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=29) · [Revision 38](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=38)

The search covered the preceding family revision and sign, unit and rank calculations in the related literature. I also searched three pinned contemporary source trees for the new theorem identifiers and for cyclotomic units mentioned next to tame inertia or ray characters. No matching formal derivation appeared in those searches. This establishes the addition to this family. Equivalent arguments under other names remain possible. [Previous family revision](https://github.com/leecrossley/prime-window-rh-criterion/tree/6ff0f17a7ce0f1a42ae75d60536a032f90153422/results/geometric-window-descent) · [Sanftenberg](https://github.com/dbsanfte/RiemannGaussian/tree/bbcc0615a14ece5e6dcc8f80714e7a1e1cdd77b6) · [Brox](https://github.com/JoseBrox/GRH_distillation/tree/a15e1c073a08aeb79e0b199867d75d70e65a66b2) · [Lattice comparison](https://github.com/twinheterodox/three-simplifications-dirichlet-grh/tree/4dc189a9aa34db3bb7e67b5ad04abe781ff12995)
