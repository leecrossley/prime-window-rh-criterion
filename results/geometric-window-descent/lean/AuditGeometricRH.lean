import SecondSeedRH
import AuditSlopeGraph

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.ConductorOne.rh_from_second_seed
    [`RiemannReduction.SymplecticTwo.automorphy_of_second_seed,
     `RiemannReduction.SymplecticTwo.count_from_second_seed,
     `RiemannReduction.GaussianTower.host_tower_nine,
     `RiemannReduction.QuadraticDescent.quadratic_genus_bound,
     `RiemannReduction.QuadraticDescent.rank_le_twice_sub_one,
     `UpperTheory.V.Ws.proMod_of_pmEx_of_ctx2_of_kPair_of_star,
     `UpperTheory.V.Ws.exists_iwasawaRank_bound_of_ferreroWashington,
     `UpperTheory.V.FW.ferreroWashington, `UpperTheory.V.Win.partA,
     `GlobalTheory.T.even_theta_chain_spanned_params_of_value_independent,
     `GlobalTheory.T.theta_chain_last_step_intertwines_matched_hecke,
     `GlobalTheory.T.theta_chain_occurring_params_norm_half_rank_bound]
    [`UpperTheory.V.HV.DescentVanishingReductions.sp4In0_alt,
     `UpperTheory.V.Cu.main4_alt,
     `UpperTheory.V.Cu.modularity_rank_four_of_promodularity_case_three,
     `UpperTheory.V.Cu.promodularity_case_three_of_chain_reduction,
     `UpperTheory.V.Cu.chainIV_alt,
     `UpperTheory.V.Z.Win.Birth.fourth_initial_of_prints_h,
     `UpperTheory.V.Two.baseRk, `UpperTheory.V.Two.quadStep, `UpperTheory.V.Two.idxTwo,
     `RiemannReduction.ConductorOne.rh_of_single_inertia,
     `RiemannReduction.GaussianTower.ordinary_two_input_unconditional]
    true (some "second-rh-names.txt")
