import SingleInertiaRH
import AuditSlopeGraph

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.ConductorOne.rh_of_single_inertia
    [`RiemannReduction.GaussianTower.ordinary_two_input_unconditional,
     `UpperTheory.V.Cu.main4_alt, `UpperTheory.V.Two.baseRk]
    [`RiemannReduction.GaussianTower.host_tower_nine]
    true (some "previous-rh-names.txt")
