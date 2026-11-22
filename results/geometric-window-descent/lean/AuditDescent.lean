import NineIntegralTower
import AuditSlopeGraph

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.GaussianTower.host_tower_nine
    [`RiemannReduction.GaussianTower.pure_rank_zero,
     `RiemannReduction.QuadraticDescent.quadratic_genus_bound,
     `RiemannReduction.QuadraticDescent.exists_quadratic_transfer,
     `RiemannReduction.QuadraticDescent.rank_le_twice_sub_one,
     `RiemannReduction.GaussianTower.ordinary_ray_six, `UpperTheory.V.Two.charStep]
    [`UpperTheory.V.Two.quadStep, `UpperTheory.V.Two.idxTwo, `UpperTheory.V.Two.baseRk,
     `UpperTheory.V.Two.towerTwo, `UpperTheory.V.FW.ferreroWashington, `RiemannHypothesis]
    false (some "rank-names.txt")
