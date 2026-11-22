import RealUnitSignRows
import AuditSlopeGraph

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.UnitSigns.row_counts
    [`RiemannReduction.UnitSigns.at_q, `RiemannReduction.UnitSigns.at_d,
     `RiemannReduction.UnitSigns.cube_orbit, `RiemannReduction.UnitSigns.ninth_orbit,
     `RiemannReduction.UnitSigns.integral_units, `RiemannReduction.UnitSigns.signs_at_primes,
     `RiemannReduction.UnitResidue.prime_counts, `RiemannReduction.UnitResidue.zeta_nonsquare,
     `IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq]
    [`RiemannHypothesis, `RiemannReduction.Mizusawa.RankThree, `UpperTheory.V.FW.ferreroWashington]
    false (some "real-unit-row-names.txt")
