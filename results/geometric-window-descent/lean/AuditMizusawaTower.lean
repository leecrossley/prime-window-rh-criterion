import MizusawaTower
import AuditSlopeGraph

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.Mizusawa.host_tower_three
    [`RiemannReduction.Mizusawa.RankThree, `RiemannReduction.Mizusawa.host_eq_radicals,
     `RiemannReduction.Mizusawa.radical_eq_genus, `UpperTheory.V.CF.gauss,
     `RiemannReduction.Mizusawa.descend,
     `RiemannReduction.Mizusawa.evaluations_injective, `UpperTheory.V.Two.genLE_of_abRk]
    [`RiemannHypothesis, `RiemannReduction.GaussianTower.ordinary_ray_six,
     `RiemannReduction.GaussianTower.host_rank_nine, `UpperTheory.V.FW.ferreroWashington]
    false (some "mizusawa-rank-names.txt")
