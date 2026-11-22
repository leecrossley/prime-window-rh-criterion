import CaseTwoAutomorphy
import SymplecticTwoCount
import SymplecticTwoData
import PrincipalLocalCounts
import PrincipalTwoConductor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ConductorAtMapInjectiveCoeff

/-! The second symplectic count directly at the ordinary character. The datum's
auxiliary odd modulus is one, and only its first dyadic conductor is needed.
The symplectic automorphy, rigidity, cohomology and counting suppliers remain
those of Alpöge's argument. -/
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
namespace RiemannReduction.SymplecticTwo
open RiemannReduction.ConductorOne

private theorem second_from_seed_with_roots (hA : CaseTwoAutomorphy) (hP : CohomologyHyp) (hM : LemmaM) (hM' : LemmaM') (hLP : LemmaP) (hN : _root_.UpperTheory.V.Af.NumberSp4Alt)
    (hAd : _root_.UpperTheory.V.Th.RigiditySymplecticFour) (hX : X.CorX)
    (hSo : ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], SoV Ω l ∧ SoFin Ω l)
    : ∃ C : ℕ, ∀ h : Host, h.chi = PChar.one → ∀ t : ℕ, h.Big t →
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ),
      l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, h.CaseII l e ψ →
      HasEnoughRootsOfUnity c.O (2 ^ h.nII l ψ) →
      VLe Ω c e ψ (((l : ℝ) * h.N * e) ^ C) := by
  obtain ⟨C, A, hc⟩ := _root_.UpperTheory.V.Z.Win.A4.exists_frob_nonvanishing_with_sha_bound hN
  refine ⟨2*C+8*A+22, fun h one t ht Ω _ _ _ l hl c e hl2 he0 het ψ hψ hcase roots => ?_⟩
  obtain ⟨D, hD, hO⟩ := data_of_case_two hX Ω h l c e hl2 ψ hψ hcase roots
  have hOf : Aut.OfCase D h e ψ := Or.inl ⟨hcase,hO⟩
  have second : Ctx2 D := ⟨hD,h,t,e,ψ,ht,he0,het,hψ,hcase,hO⟩
  obtain ⟨hF, hNE, ι, hAU⟩ := hA D second
  have hctx : Ctx2 D ∨ Ctx3 D := Or.inl second
  have hsha := shaEq Ω h t ht l c e hl2 he0 het ψ hψ D hD hOf
  obtain ⟨M⟩ := exModel D hD hLP (phiGam D hD hP) (nums D hD hP) (locBase D hD hP.loc)
  have ho : 0 < h.o := (hostIndex h).2.2.2.1
  have hlp := hl.out
  let n' := h.nII l ψ
  let p₁ : ℕ := 1
  have hn' : c2 ψ ≤ n' := by
    have h1 : 2 ^ c2 ψ ≤ max (l * h.N * 4 ^ n0 l ψ) (2 ^ (c2 ψ + 6) * h.o * l ^ 3 * h.q ^ 2) := by
      refine le_trans ?_ (le_max_right _ _)
      have hq : 0 < h.q := NeZero.pos _
      have := hlp.pos
      rw [pow_add, mul_assoc, mul_assoc, mul_assoc]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have h2 := Nat.clog_mono_right 2 h1
    rwa [Nat.clog_pow 2 _ (by norm_num)] at h2
  obtain ⟨⟨k1, k2, k3⟩, o1, o2, o3⟩ := levOf Ω h t ht l c e hl2 he0 het ψ hψ D hD n' p₁ 1 hO hn' (one_dvd _)
  have hp₁ : 0 < p₁ := by
    obtain ⟨a, -⟩ := hO.xi
    exact NeZero.pos _
  have hNp := h.N_pos
  have hlpos := hlp.pos
  obtain ⟨q1, q2, q3, -⟩ := pZeroLe (l * h.N * p₁) (by positivity)
  have q4 : ¬ pZero (l * h.N * p₁) ∣ 2 := fun hd => by have := Nat.le_of_dvd two_pos hd; omega
  have q5 : ¬ pZero (l * h.N * p₁) ∣ l * 2 ^ n' * h.N * p₁ := fun hd => by
    rw [show l * 2 ^ n' * h.N * p₁ = 2 ^ n' * (l * h.N * p₁) by ring] at hd
    exact ((Nat.Prime.dvd_mul q1).1 hd).elim (fun a => q4 (q1.dvd_of_dvd_pow a)) q3
  have q6 : pZero (l * h.N * p₁) ∉ D.S := fun hd => by
    rw [hO.S_eq] at hd
    have hd := Nat.dvd_of_mem_primeFactors hd
    rw [show 2 * l * h.N * p₁ = 2 * (l * h.N * p₁) by ring] at hd
    exact ((Nat.Prime.dvd_mul q1).1 hd).elim q4 q3
  have hlev : 1 ≤ l * 2 ^ n' * h.N * p₁ := Nat.pos_of_ne_zero (by positivity)
  have hk : 0 < (l - 1) * 2 ^ n' * (2 * h.o) := by
    have : 0 < l - 1 := Nat.sub_pos_of_lt hlp.one_lt
    positivity
  obtain ⟨σ, hσ, hle⟩ := hc D hD _ hlev k1 k2 k3 _ hk o1 o2 o3 _ q1 q2 q5 q6 ι hAU
  have hI : D.Ineq σ := galoisRep_ineq_of_allIrreducible_nonvanishing D hD M hM hM' hP.loc (hSo Ω l).1 (hSo Ω l).2 hF hNE
    (fun r hr hi => hAd Ω l c D hctx _ hlev k1 k2 k3 ι r hr hi (hAU r hr hi)) σ hσ
  have hb := principal_level_budget C A h one l c e hl2 he0 ψ (h.mem_X.1 hψ).1
  have hle' := hle hI
  rw [hO.e_eq] at hle'
  refine ⟨ne_top_of_le_ne_top hI.1 hsha, le_trans ?_ (hle'.trans hb)⟩
  exact mul_le_mul_of_nonneg_right (Chr.nrm_mono l hsha hI.1) (Real.log_natCast_nonneg l)

theorem count_from_second_seed :
    CaseTwoAutomorphy → CohomologyHyp → LemmaM → LemmaM' → LemmaP → _root_.UpperTheory.V.Af.NumberSp4Alt → _root_.UpperTheory.V.Th.RigiditySymplecticFour → X.CorX → (∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], SoV Ω l ∧ SoFin Ω l) → SecondCaseAt PChar.one := by
  intro hA hP hM hM' hLP hN hAd hX hSo
  obtain ⟨C, hC⟩ := second_from_seed_with_roots hA hP hM hM' hLP hN hAd hX hSo
  refine ⟨C, fun h one t ht Ω _ _ _ l _ c e hl2 he0 het ψ hψ hcase => ?_⟩
  obtain ⟨c₁, h₁⟩ := exists_coef l (2 ^ h.nII l ψ)
  obtain ⟨c', hc, hc₁⟩ := (coefSup l).1 c c₁
  have roots := enough_of_le hc₁ (2 ^ h.nII l ψ)
  let f : c.O →+* c'.O := (Subalgebra.inclusion hc).toRingHom
  have hf : Function.Injective f := Subalgebra.inclusion_injective hc
  have e2 : h.nII l (chHom f ψ) = h.nII l ψ := by
    unfold Host.nII
    rw [conductor_at_map_injective_coeff f hf, parity_at_map_injective_coeff f hf]
  have hψ' : chHom f ψ ∈ h.X c' e := by
    rw [h.mem_X] at hψ ⊢
    refine ⟨?_, (chHom_even f hf e ψ).2 hψ.2⟩
    unfold Host.IsChar
    rw [chHom_ker f hf]
    exact hψ.1
  have hcase' : h.CaseII l e (chHom f ψ) := by
    refine ⟨hcase.1, ?_, hcase.2.2⟩
    unfold EV
    rw [← chHom_chiP f hf, chHom_ord f hf]
    exact hcase.2.1
  have hV := hC h one t ht Ω l c' e hl2 he0 het _ hψ' hcase' (e2.symm ▸ roots)
  obtain ⟨a,b⟩ := coefIndep Ω l c c' h.N e ψ (chHom f ψ) fun _ => rfl
  exact ⟨fun h0 => hV.1 (a.1 h0), b ▸ hV.2⟩
end RiemannReduction.SymplecticTwo
end
