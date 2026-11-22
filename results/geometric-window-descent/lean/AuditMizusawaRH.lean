import MizusawaWindowRH
import AuditSlopeGraph

example : RiemannReduction.Mizusawa.RankThree → RiemannHypothesis :=
  RiemannReduction.ConductorOne.rh_of_mizusawa_rank_three

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.ConductorOne.rh_of_mizusawa_rank_three
    [`RiemannReduction.Mizusawa.RankThree,
     `RiemannReduction.Mizusawa.host_eq_radicals, `RiemannReduction.Mizusawa.negative_radical,
     `RiemannReduction.Mizusawa.radical_eq_genus,
     `RiemannReduction.Mizusawa.character_bound_of_free, `RiemannReduction.Mizusawa.descend,
     `RiemannReduction.Mizusawa.host_tower_three, `RiemannReduction.Mizusawa.ordinary_three_input,
     `RiemannReduction.SymplecticTwo.automorphy_of_second_seed,
     `UpperTheory.V.FW.ferreroWashington, `UpperTheory.V.Win.partA,
     `GlobalTheory.T.even_theta_chain_spanned_params_of_value_independent,
     `GlobalTheory.T.theta_chain_last_step_intertwines_matched_hecke,
     `GlobalTheory.T.theta_chain_occurring_params_norm_half_rank_bound]
    [`RiemannReduction.GaussianTower.host_tower_nine, `RiemannReduction.GaussianTower.host_rank_nine,
     `RiemannReduction.GaussianTower.ordinary_ray_six, `RiemannReduction.GaussianTower.ordinary_nine_input,
     `RiemannReduction.QuadraticDescent.quadratic_genus_bound,
     `RiemannReduction.QuadraticDescent.rank_le_twice_sub_one,
     `RiemannReduction.ConductorOne.rh_from_second_seed,
     `UpperTheory.V.HV.DescentVanishingReductions.sp4In0_alt,
     `UpperTheory.V.Cu.chainIV_alt, `UpperTheory.V.Two.baseRk]
    false (some "mizusawa-rh-names.txt")
