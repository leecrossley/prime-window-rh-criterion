import CyclotomicEight
import AuditSlopeGraph

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.TameSigns.host_tower_three
    [`RiemannReduction.TameSigns.finite_ray_eight, `RiemannReduction.TameSigns.host_eight,
     `RiemannReduction.UnitSigns.row_counts, `RiemannReduction.UnitSigns.sign_places,
     `RiemannReduction.TameSigns.detects_finite_inertia, `RiemannReduction.TameSigns.absolute_inertia_iff,
     `RiemannReduction.TameSigns.finite_pair_equal, `RiemannReduction.UnitParity.global_unit_parity,
     `UpperTheory.V.CF.ineAbs, `RiemannReduction.GaussianTower.TameSites.ray_rank_three,
     `RiemannReduction.GaussianTower.host_rank_of_cofinal_finite_ray, `UpperTheory.V.Two.genLE_of_abRk]
    [`RiemannHypothesis, `RiemannReduction.Mizusawa.RankThree, `RiemannReduction.Mizusawa.host_tower_three,
     `RiemannReduction.GaussianTower.host_rank_nine, `UpperTheory.V.FW.ferreroWashington]
    false (some "tame-eight-names.txt")
