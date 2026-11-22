import MizusawaNineControl
import AuditSlopeGraph

example : RiemannReduction.Mizusawa.RankThree → RiemannHypothesis :=
  RiemannReduction.ConductorOne.rh_of_mizusawa_at_nine

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.ConductorOne.rh_of_mizusawa_at_nine
    [`RiemannReduction.Mizusawa.nine_input_from_three, `RiemannReduction.Mizusawa.host_rank_three,
     `RiemannReduction.Mizusawa.host_eq_radicals, `RiemannReduction.Mizusawa.character_bound_of_free,
     `UpperTheory.V.Two.XRk.mono, `UpperTheory.V.Win.partA]
    [`RiemannReduction.GaussianTower.ordinary_nine_input, `RiemannReduction.Mizusawa.ordinary_three_input,
     `RiemannReduction.ConductorOne.rh_of_mizusawa_rank_three,
     `RiemannReduction.ConductorOne.rh_from_second_seed]
    false (some "mizusawa-control-names.txt")
