# Verification record

The development build of 22 November 2026 compiled `SecondSeedRH` with both `rh_from_second_seed` and a square-block corollary. The standalone kernel replayed that module and `CofinalRayLayers`. Two separate audit modules, `AuditSecondSeedRH` and `AuditSecondSeedWindow`, examined the closed RH theorem and the window theorem with its two input hypotheses. The former reached 1,476,889 declarations and used only `propext`, `Classical.choice` and `Quot.sound`. The baseline count came from `ReferenceDependencyAudit`. [Development build and audits](evidence/checked-geometric-rh.txt) [Baseline run](evidence/checked-reference-rh.txt)

The distributed `SecondSeedRH` ends at the closed RH theorem. The logs above predate the distributed replay scripts. The `proof` target checks the distributed theorem, `window` checks the earlier conditional statement and `compare` checks both together with the two reference endpoints. [Distributed theorem](lean/SecondSeedRH.lean) [Replay instructions](REPLAY.md)

## Arithmetic and automorphy

The `rank` command in this package was run from a fresh object directory. It built the nine-generator and previous 24-generator statements and independently replayed six modules in `leanchecker`. The audit of `host_tower_nine` reached 77,321 declarations. Its excluded dependencies include `RiemannHypothesis`, Ferrero–Washington and the former `baseRk`, `quadStep`, and `idxTwo` tower bounds. [Fresh arithmetic replay](evidence/rank-replay.txt) · [Arithmetic audit](lean/AuditDescent.lean)

The cohomology-window audit reached 390,211 declarations, including the case-two automorphy and count theorems. At this stage the window theorem takes a tower input and a literature hypothesis. The closed RH proof supplies both and uses the nine-generator bound. Its dependencies include the three theta comparisons and Ferrero–Washington at odd residual primes. The case-three promodularity chain, fourth seed and former tower bounds drop out. [Recorded audits](evidence/checked-geometric-rh.txt) [Window theorem](lean/SecondSeedWindow.lean) [Window audit](lean/AuditSecondSeedWindow.lean) [Named comparisons](evidence/comparison.json)

The three retained comparisons transport a matched Hecke operator through the last theta lift, bound the spectral parameters occurring at the end of the chain, and control the parameters spanned by an even chain. These are three audit entries in a larger geometric construction. [Last theta lift](https://github.com/Deicyde/riemann-hypothesis/blob/e7c8972c701d3396947808ab20cc16dc14623d33/src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaChainLastStepIntertwinesMatchedHeckeStatement.lean) · [Occurrence bound](https://github.com/Deicyde/riemann-hypothesis/blob/e7c8972c701d3396947808ab20cc16dc14623d33/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaChainOccurringParamsNormHalfRankBoundStatement.lean) · [Even-chain span](https://github.com/Deicyde/riemann-hypothesis/blob/e7c8972c701d3396947808ab20cc16dc14623d33/src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EvenThetaChainSpannedParamsOfValueIndependentStatement.lean)

## Checking the comparison

| Endpoint | Count | SHA-256 of sorted names |
| --- | ---: | --- |
| Published principal-character geometry | 1,477,932 | `fe8f4bbbcae744c5faf261b2971f98f54023ecb191717033c5407e4e1e72b7a3` |
| Previous 24-generator calculation | 1,477,680 | `80c2d0d5542489e68494164c2f14f406588eecf5b74963c9c116013ccc4756c6` |
| Nine generators and case-two automorphy | 1,476,889 | `b13bdd252156bae867953398f17cb4c90fb704dbf33fb603d3c5fa5eb8a2bf72` |

The two comparisons and all four complete declaration differences were reproduced from the recorded name lists when preparing this note. The `compare` replay regenerates all three lists from the Lean endpoints, checks their hashes, and compares the complete differences. The public note includes the proof sources and only the differences between the full lists. [Published baseline audit](evidence/checked-reference-rh.txt) · [Previous calculation](evidence/checked-24-generator-rh.txt) · [Comparison program](compare.py)

The separate square-block corollary applies the collection’s implication from RH. The note records the remaining problem of proving the cancellation estimate directly from the signed sum. [Square-bound implication](../prime-window-power-samples/pairs/mobius/lean/SquareSignedConverse.lean) [Open arithmetic estimate](../prime-window-power-samples/pairs/mobius/CUTOFFS.md)
