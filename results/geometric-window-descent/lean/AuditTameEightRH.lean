import TameEightWindowRH
import AuditSlopeGraph

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.ConductorOne.rh_from_tame_units
    [`RiemannReduction.TameSigns.ordinary_three_input, `RiemannReduction.TameSigns.host_tower_three,
     `RiemannReduction.TameSigns.finite_ray_eight, `RiemannReduction.TameSigns.finite_pair_equal,
     `RiemannReduction.UnitSigns.row_counts, `UpperTheory.V.CF.ineAbs,
     `UpperTheory.V.FW.ferreroWashington, `UpperTheory.V.Win.partA]
    [`RiemannReduction.Mizusawa.RankThree, `RiemannReduction.Mizusawa.host_tower_three,
     `RiemannReduction.GaussianTower.host_rank_nine, `RiemannReduction.GaussianTower.ordinary_nine_input,
     `RiemannReduction.ConductorOne.rh_from_second_seed, `RiemannReduction.ConductorOne.rh_of_mizusawa_rank_three]
    true (some "tame-eight-rh-names.txt")
