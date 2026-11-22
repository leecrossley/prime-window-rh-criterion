import UnconditionalTower
import NoOddLayerWindow
import SingleTowerGrid

/-! The odd-prime plus bound is valid pointwise. Only the prime-two exceptional
indices enter the simultaneous interval selection at the ordinary character. -/
noncomputable section
open NumberField Formalism.ConjugateSelfDual Formalism.HC Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.HV
namespace RiemannReduction.PrincipalLayer
open RiemannReduction.ConductorOne

theorem window_from_single_inertia
    (lit : GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : VWinAt PChar.one 401 := by
  let H := HV.DescentVanishingReductions.published_hypotheses_from_patching_alt lit Z.Tf.SR.descWeak
  have generators := ZK.lemmaK_litN_alt H.litN
  have ends := Z.Win.Dn.ends0_alt H
  have first := Z.J.count_i_of_printed_bound_k_kato_automorphy H generators
    (Z.Kato.WeilSphericalRecords.katoTwoW_of_printsH H)
    (HV.Core0.automorphyUnramified_of_litN_of_gdEnd H.litN ends.1)
  have fifth := Z.J.count_v_of_printed_bound_k_reduced_unitary_lift H generators ends.2
  have duality := HV.U.pt_s H.litN
  have generatorExists := generators
  obtain ⟨C,generators⟩ := generators
  have liftInputs := HV.DescentVanishingReductions.adjoint_lift_of_prints H
  have lifting := HV.DescentVanishingReductions.adjoint_lifting_of_cohomology H
  have second := RiemannReduction.SymplecticTwo.count_principal_case_two
    (HV.DescentVanishingReductions.sp4In0_alt H) liftInputs.coh
    Alg.M.main_holds Alg.M.mprime_holds Alg.lemmaP
    (UpperTheory.GalN.V.numberSp4_n_alt H.toClassicalTheorems)
    (Th.rigSp4_alt liftInputs lifting) (X.corX X.lemmaX X.residual_bernoulli_nonvanishing)
    (fun Ω _ _ _ l _ => ⟨X.soBar C generators duality H.litN.coh.lfK H.litN.coh.ltK ℚ Ω l,
      fun co => X.soFin C generators duality H.litN.coh.lfK H.litN.coh.ltK ℚ Ω l co.O⟩)
  have small := countVs duality H.litN.coh.lfK H.litN.coh.ltK _ generators
  have odd := polynomial_odd_plus first second fifth small (HV.countZ X.propZ)
  have towers : Two.TowerBound := fun l _ L _ _ R h => PropA.aBound_of_isTower duality H.litN.coh.lfK H.litN.coh.ltK l L R h
  have two := single_tower_grid (AbF.ofChar PChar.one) (by norm_num : (1:ℝ)≤401) generatorExists (RiemannReduction.GaussianTower.ordinary_two_input_unconditional towers)
  exact principal_window_of_joint_pages (by norm_num) (pages_from_two 401 (by norm_num) odd two)
#print axioms window_from_single_inertia
end RiemannReduction.PrincipalLayer
