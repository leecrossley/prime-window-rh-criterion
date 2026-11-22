import AbelianLayerVanishing
import SevenCyclotomic
import PrincipalInsideThree

/-! The class number of the seventh cyclotomic field pays for every remaining
trivial-character twist at 7. The pointwise bounds can then be summed without a tower. -/
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Odd UpperTheory.V.ML
open IntermediateField UpperTheory.V.X
namespace RiemannReduction.CyclotomicLayer

theorem length_at_seven (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[7] O] [Module.Finite ℤ_[7] O]
    (e : ℕ) (positive : 1 ≤ e) : Chr.V 7 e (1 : G ℚ Ω →* Oˣ) = 0 := by
  have prime : Fact (Nat.Prime 7) := ⟨by decide⟩
  by_cases full : 6 ∣ e
  · exact zOne Ω 7 O (by decide) e positive full
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : ∀ i, HasEnoughRootsOfUnity Ω (7 ^ i) := fun i => inferInstance
  obtain ⟨ζ, primitive⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω 7
  let K := ℚ⟮ζ⟯
  have : FiniteDimensional ℚ K := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have : NumberField K := NumberField.of_module_finite ℚ K
  have : IsCyclotomicExtension {7} ℚ K := primitive.intermediateField_adjoin_isCyclotomicExtension ℚ
  have fixed (g : G ℚ Ω) : g ∈ galOf ℚ K Ω ↔ g ζ = ζ := by
    refine ⟨fun hg => hg (AdjoinSimple.gen ℚ ζ), fun hg x => ?_⟩
    have contained : K ≤ fixedField (Subgroup.zpowers g) := by
      rw [adjoin_simple_le_iff,mem_fixedField_iff]
      intro f hf
      exact (Subgroup.zpowers_le.2 (show g ∈ MulAction.stabilizer (G ℚ Ω) ζ from hg)) hf
    exact (mem_fixedField_iff _ _).1 (contained x.2) g (Subgroup.mem_zpowers g)
  let power (g : G ℚ Ω) := (PadicInt.toZModPow 1 (cycZ ℚ Ω 7 g : ℤ_[7])).val
  have action (g : G ℚ Ω) : g ζ = ζ ^ power g :=
    cyclotomicCharacter.spec 7 (n:=1) g.toRingEquiv ζ (by rw [pow_one,primitive.pow_eq_one])
  apply vanish_at_abelian_field Ω 7 O (by decide) e full K (by rw [class_number_seventh K]; simp)
  · intro g hg
    have eqn : ζ ^ power g = ζ ^ 1 := (action g).symm.trans (((fixed g).1 hg).trans (pow_one ζ).symm)
    have modEq := (primitive.isOfFinOrder (by decide)).pow_eq_pow_iff_modEq.mp eqn
    rw [← primitive.eq_orderOf] at modEq
    have cast : ((power g : ℕ) : ZMod 7) = 1 := by
      simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff (power g) 1 7).2 modEq
    rw [← zq_cast (cycZ ℚ Ω 7 g : ℤ_[7]), cast, one_pow]
  · intro a b
    apply (fixed _).2
    change (a*b).symm ((b*a) ζ) = ζ
    apply (a*b).symm_apply_eq.mpr
    calc (b*a) ζ = (ζ ^ power b)^power a := by simp only [AlgEquiv.mul_apply, action a, map_pow, action b]
         _ = (ζ ^ power a)^power b := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
         _ = (a*b) ζ := by simp only [AlgEquiv.mul_apply, action b, map_pow, action a]

open RiemannReduction.ConductorOne in
theorem all_case_four_seven {h : UpperTheory.V.HV.Host} (one : h.chi = PChar.one) {t : ℕ} (big : h.Big t)
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (c : Coef 7)
    {e : ℕ} {ψ : DirichletCharacter c.O h.N} (member : ψ ∈ h.X c e) (fourth : h.CaseIV 7 e ψ) :
    Vlen Ω c e ψ = 0 := by
  have := c.dvr
  have := c.fin
  have small := (bchiFacts h t big).1 7 fourth.1
  obtain rfl := case_four_is_trivial one (h.mem_X.1 member).1 (by decide : Nat.Prime 7) (by decide) small.1.ne small.2.ne fourth
  have eqn : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O h.N) = 1 := by ext g; simp [Chr.dirG]
  unfold Vlen
  rw [eqn]
  exact le_antisymm ((Chr.V'_le_V 7 h.N e 1).trans
    (length_at_seven Ω c.O e (by have := fourth.2.1; omega)).le) bot_le

#print axioms length_at_seven
#print axioms all_case_four_seven
end RiemannReduction.CyclotomicLayer
