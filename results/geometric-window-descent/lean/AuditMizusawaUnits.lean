import MizusawaUnitParity
import AuditSlopeGraph

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.UnitParity.global_unit_parity
    [`GroundTheory.Global.ideleSymbol_diagonal, `GroundTheory.Global.units_le_ker_localSymbol,
     `GroundTheory.Global.infiniteLocalSymbol_of_not_isReal]
    [`RiemannHypothesis, `UpperTheory.V.FW.ferreroWashington, `RiemannReduction.Mizusawa.RankThree]
    false (some "unit-parity-names.txt")
