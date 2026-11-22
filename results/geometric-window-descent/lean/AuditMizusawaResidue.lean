import MizusawaUnitResidue
import AuditSlopeGraph

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.UnitResidue.root_of_unity_row
    [`RiemannReduction.UnitResidue.orders, `RiemannReduction.UnitResidue.prime_counts,
     `RiemannReduction.UnitResidue.not_square, `FiniteField.pow_card_sub_one_eq_one,
     `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd, `IsPrimitiveRoot.idealQuotient_mk,
     `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn]
    [`RiemannHypothesis, `UpperTheory.V.FW.ferreroWashington, `RiemannReduction.Mizusawa.RankThree]
    false (some "root-of-unity-names.txt")
