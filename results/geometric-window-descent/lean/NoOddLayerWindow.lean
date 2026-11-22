import PrincipalOddPlus
import DyadicGoodGrid
import SymplecticTwoCount
import PrincipalArchivedWindow

/-! The odd-prime plus bound is valid pointwise. Only the prime-two exceptional
indices enter the simultaneous interval selection at the ordinary character. -/
noncomputable section
open NumberField Formalism.ConjugateSelfDual Formalism.HC Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.HV
namespace RiemannReduction.PrincipalLayer
open RiemannReduction.ConductorOne

theorem pages_from_two (Ct : ℝ) (hCt : 1 ≤ Ct) (primes : OddPlusBound)
    (dyadic : TwoGrid Ct (AbF.ofChar PChar.one)) : PrincipalJointPages Ct := by
  intro eps hp hlt e he
  let ψ := PChar.one
  let t : ℝ → ℕ := fun x => ⌊x ^ Ct⌋₊
  have ha : admitted 4 Ct e t := admissible_of_pageN hp hlt hCt he
  obtain ⟨C,r₁,r₂,_,_,odd⟩ := primes
  obtain ⟨J,start,hJ,grid⟩ := dyadic eps 4 hp hlt
  let bad := [ψ.N, ordC ψ, pK ψ, hStar ψ, pOne ψ, r₁, r₂]
  refine ⟨J,(C:ℝ),(bad.sum:ℕ),max start ((2:ℝ)^J),hJ,?_⟩
  intro X hx q d pair hq hd c c' logBound
  obtain ⟨Y,range,hTwo⟩ := grid e t ha X ((le_max_left _ _).trans hx) q d pair logBound
  refine ⟨Y,range,fun x lo hi => ⟨hTwo x lo hi,?_⟩⟩
  have left : (2:ℝ) ≤ X^(1/J) := by
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) J) ((le_max_right _ _).trans hx)
        (by positivity : 0 ≤ 1/J)
    rw [one_div, Real.rpow_rpow_inv (by norm_num : (0:ℝ) ≤ 2) hJ.ne'] at h1
    simpa only [one_div] using h1
  have hx2 : (2:ℝ) ≤ x := left.trans (range.1.trans lo)
  obtain ⟨he2,_,ht2,htx⟩ := ha x hx2
  have htX : (t x : ℝ) ≤ X ^ Ct := htx.trans (Real.rpow_le_rpow (by linarith) (hi.trans range.2) (by linarith))
  have hlist (y : ℕ) (mem : y ∈ bad) : y < q ∧ y < d := by
    have b := List.le_sum_of_mem mem
    exact ⟨b.trans_lt (by exact_mod_cast c), b.trans_lt (by exact_mod_cast c')⟩
  have hh : UpperTheory.V.HV.Host.Big ⟨ψ,e x,q,d,he2,pair⟩ (t x) := by
    refine ⟨by exact_mod_cast (show (2*(t x:ℝ)+1) < q by linarith),
      by exact_mod_cast (show (2*(t x:ℝ)+1) < d by linarith), ?_⟩
    intro y hy
    apply hlist y
    simp only [bad,Host.q,Host.o,List.mem_cons,List.not_mem_nil] at hy ⊢
    tauto
  intro E _ _ _ hE Ω _ _ _ ld
  have use := odd ⟨ψ,e x,q,d,he2,pair⟩ rfl
    (hlist r₁ (by simp [bad])).1 (hlist r₁ (by simp [bad])).2
    (hlist r₂ (by simp [bad])).1 (hlist r₂ (by simp [bad])).2 (t x) ht2 hh E hE Ω ld
  refine ⟨use.1, fun S hS => ?_⟩
  rw [hostCond ⟨ψ,e x,q,d,he2,pair⟩ E hE, Real.rpow_natCast]
  exact (use.2 S hS).trans (le_add_of_nonneg_right (by positivity))

theorem window_from_dyadic_grid
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
  have two := dyadic_grid (AbF.ofChar PChar.one) (by norm_num : (1:ℝ)≤401) generatorExists (Two.twoIn FW.ferreroWashington towers)
  exact principal_window_of_joint_pages (by norm_num) (pages_from_two 401 (by norm_num) odd two)
#print axioms window_from_dyadic_grid
end RiemannReduction.PrincipalLayer
