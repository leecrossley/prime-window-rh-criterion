# Verification record

The standalone Lean kernel replayed the closed geometric RH theorem on 22 November 2026. The declaration audit found exactly Mathlib’s `RiemannHypothesis` at its root and only `propext`, `Classical.choice`, and `Quot.sound` among its axioms. The archived geometric library and Mathlib were supplied as checked inputs. Their public revisions and the commands to rebuild the specialization are in the replay instructions. [Geometric build, kernel output and audit](evidence/checked-geometric-rh.txt) · [Replay](REPLAY.md)

## Arithmetic and automorphy

The `rank` command in this package was run from a fresh object directory. It built the nine-generator and previous 24-generator statements and independently replayed six modules in `leanchecker`. The audit of `host_tower_nine` reached 77,321 declarations. Its excluded dependencies include `RiemannHypothesis`, Ferrero–Washington and the former `baseRk`, `quadStep`, and `idxTwo` tower bounds. [Fresh arithmetic replay](evidence/rank-replay.txt) · [Arithmetic audit](lean/AuditDescent.lean)

The cohomology-window audit, taken before applying the nine-generator theorem, reached 390,211 declarations. It retains the case-two promodularity argument. The closed RH audit follows the application to the unconditional tower bound. Three theta comparisons and Ferrero–Washington at odd residual primes remain reachable. The case-three promodularity chain, fourth seed and the former tower bounds drop out. [Window and closed RH audits](evidence/checked-geometric-rh.txt) · [Named membership checks](evidence/comparison.json)

The three retained comparisons transport a matched Hecke operator through the last theta lift, bound the spectral parameters occurring at the end of the chain, and control the parameters spanned by an even chain. These are three audit entries in a larger geometric construction. [Last theta lift](https://github.com/Deicyde/riemann-hypothesis/blob/e7c8972c701d3396947808ab20cc16dc14623d33/src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaChainLastStepIntertwinesMatchedHeckeStatement.lean) · [Occurrence bound](https://github.com/Deicyde/riemann-hypothesis/blob/e7c8972c701d3396947808ab20cc16dc14623d33/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainOccurringParamsNormHalfRankBoundStatement.lean) · [Even-chain span](https://github.com/Deicyde/riemann-hypothesis/blob/e7c8972c701d3396947808ab20cc16dc14623d33/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EvenThetaChainSpannedParamsOfValueIndependentStatement.lean)

## Checking the comparison

| Endpoint | Count | SHA-256 of sorted names |
| --- | ---: | --- |
| Published principal-character geometry | 1,477,932 | `fe8f4bbbcae744c5faf261b2971f98f54023ecb191717033c5407e4e1e72b7a3` |
| Previous 24-generator calculation | 1,477,680 | `80c2d0d5542489e68494164c2f14f406588eecf5b74963c9c116013ccc4756c6` |
| Nine generators and case-two automorphy | 1,476,889 | `b13bdd252156bae867953398f17cb4c90fb704dbf33fb603d3c5fa5eb8a2bf72` |

The two comparisons and all four complete declaration differences were reproduced from the recorded name lists when preparing this note. The `compare` replay regenerates all three lists from the Lean endpoints, checks their hashes, and compares the complete differences. The public note includes the proof sources and only the differences between the full lists. [Published baseline audit](evidence/checked-reference-rh.txt) · [Previous calculation](evidence/checked-24-generator-rh.txt) · [Comparison program](compare.py)

The geometry-only source files stop at the RH conclusion. The original run also checked a square-block corollary obtained by applying this repository’s implication from RH. That implication and the open direct cancellation problem are recorded in the note. [Square-bound implication](../prime-window-power-samples/pairs/mobius/lean/SquareSignedConverse.lean) · [Open arithmetic estimate](../prime-window-power-samples/pairs/mobius/CUTOFFS.md)
