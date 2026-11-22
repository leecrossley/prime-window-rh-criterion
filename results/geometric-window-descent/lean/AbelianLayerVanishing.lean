import AtCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ZqField

/-! The normalized-cocycle argument of ZqField works over any finite abelian
field that kills the residual twist and has class number prime to the residual characteristic. -/
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X
namespace RiemannReduction.CyclotomicLayer

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in #[`zq_gen,`zq_unit,`zq_dvd,`zq_cast] do
    RiemannReduction.CharacterRestriction.nameHelper
      `Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ZqField n
      (`RiemannReduction.CyclotomicLayer ++ n)

/-- The unramified character has order dividing both the residue prime and the class number. -/
private theorem coprime_class_hom (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) (hp : l.Prime) (hc : l.Coprime (classNumber K))
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (h2 : ∀ m : M, 2 • m = 0 → m = 0)
    (φ : galOf ℚ K Ω → M) (hφ : φ ∈ Kum.XDual l (galOf ℚ K Ω) R M) (u : galOf ℚ K Ω) (hu : l • φ u = 0) : φ u = 0 := by
  rw [← Kum.pullOnto ℚ Ω K _ le_rfl l R M hp.ne_zero le_rfl (Or.inr h2)] at hφ
  obtain ⟨θ, hθ, rfl⟩ := hφ
  rw [Kum.clPull_apply] at hu ⊢
  generalize Kum.artCl K Ω (Kum.toGal K le_rfl u) = c at hu ⊢
  let θ' : ClassGroup (𝓞 K) →* Multiplicative M := MonoidHom.mk' (fun c => Multiplicative.ofAdd (θ c)) fun a b => by
    rw [hθ.1, ofAdd_add]
  have h1 : classNumber K • θ c = 0 := by
    have : θ' (c ^ classNumber K) = 1 := by rw [classNumber, pow_card_eq_one, map_one]
    rw [map_pow] at this
    exact this
  have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hu) (addOrderOf_dvd_of_nsmul_eq_zero h1)
  rw [hc.gcd_eq_one, Nat.dvd_one, AddMonoid.addOrderOf_eq_one_iff] at this
  exact this


/-- Vanishing follows by restricting to the chosen field and comparing the
two orders of multiplication by an inertia element on which the twist is nontrivial. -/
theorem vanish_at_abelian_field (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hp : Fact l.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (hl : 3 ≤ l) (e : ℕ) (h2 : ¬ l - 1 ∣ e)
    (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (hclass : l.Coprime (classNumber K))
    (hpow : ∀ g : G ℚ Ω, g ∈ galOf ℚ K Ω → PadicInt.toZMod (cycZ ℚ Ω l g : ℤ_[l]) ^ e = 1)
    (comm : ∀ a b : G ℚ Ω, (a*b)⁻¹*(b*a) ∈ galOf ℚ K Ω) : Chr.V l e (1 : G ℚ Ω →* Oˣ) = 0 := by
  obtain ⟨u, hu⟩ := zq_gen h2
  obtain ⟨A₀, hA₀⟩ := (B3.placesQ Ω).1 l hp.out
  obtain ⟨δ, -, hδ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A₀ hA₀ u
  set α : G ℚ Ω →* Oˣ := (1 : G ℚ Ω →* Oˣ)⁻¹ * chiO ℚ Ω l O ^ (-(e : ℤ)) with hα
  have hαg : ∀ g, α g = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ ℚ Ω l g ^ e)⁻¹ := fun g => by
    simp [hα, chiO]
  have hαs : ∀ g, (α g : O) - 1 = algebraMap ℤ_[l] O (-((cycZ ℚ Ω l g ^ e)⁻¹ : ℤ_[l]ˣ) * ((cycZ ℚ Ω l g : ℤ_[l]) ^ e - 1)) :=
    fun g => by
      rw [hαg, ← Units.val_pow_eq_pow_val, mul_sub, neg_mul, Units.inv_mul, map_sub]
      simp [sub_eq_neg_add, add_comm]
  have hun : ∀ g, cycZ ℚ Ω l g = u → IsUnit ((α g : O) - 1) := fun g hg => by
    rw [hαs, hg]
    refine IsUnit.map _ ((Units.isUnit _).neg.mul (zq_unit _ ?_))
    rw [map_sub, map_pow, map_one]
    exact sub_ne_zero.2 hu
  have htr : ∀ g : G ℚ Ω, g ∈ galOf ℚ K Ω → ∀ m : QO l O, l • m = 0 → (α g : O) • m = m := fun g hg m hm => by
    obtain ⟨y, hy⟩ := zq_dvd ((cycZ ℚ Ω l g : ℤ_[l]) ^ e - 1) (by rw [map_sub, map_pow, map_one, hpow g hg, sub_self])
    have : ((α g : O) - 1) • m = 0 := by
      rw [hαs, hy, mul_left_comm, map_mul, map_natCast, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, hm, smul_zero]
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have hin : ∀ A : ValuationSubring Ω, ¬ Over A l → ∀ g ∈ Ine (F := ℚ) A, α g = 1 := fun A hA g hg => by
    have : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hA hg
    rw [hαg, this, one_pow, inv_one, map_one]
  have htwo : ∀ m : QO l O, 2 • m = 0 → m = 0 := fun m hm => by
    have h : IsUnit ((2 : ℕ) : O) := by
      rw [← map_natCast (algebraMap ℤ_[l] O)]
      refine IsUnit.map _ (zq_unit _ ?_)
      rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => absurd (Nat.le_of_dvd two_pos h) (by omega)
    exact h.smul_eq_zero.1 ((Nat.cast_smul_eq_nsmul _ _ _).trans hm)
  have key : ∀ a : O, ∀ c ∈ ShT (QO l O) α δ l a, l • c = 0 → c = 0 := by
    rintro a c ⟨⟨hlc, hc⟩, hcδ, -, hI, hD⟩ hcl
    have hcl' : ∀ g, l • c g = 0 := fun g => congrFun hcl g
    have hdec : ∀ A : ValuationSubring Ω, Over A l → ∀ g ∈ Dec (F := ℚ) A, g ∈ galOf ℚ K Ω → c g = 0 := fun A hA g hg hgs => by
      obtain ⟨m, -, hm⟩ := hD A hA
      obtain ⟨t, ht, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
      have hlm : l • m = 0 := by
        refine (hun t htu).smul_eq_zero.1 ?_
        rw [smul_comm, sub_smul, one_smul, ← hm t (Ine_le_Dec (F := ℚ) A ht), hcl']
      rw [hm g hg, htr g hgs m hlm, sub_self]
    have hX : (fun v : galOf ℚ K Ω => c v) ∈ Kum.XDual l (galOf ℚ K Ω) O (QO l O) := by
      refine ⟨hlc.comp_continuous continuous_subtype_val, fun v w => ?_, fun A v hv => ?_, fun A hA v hv => ?_⟩
      · show c (v * w) = c v + c w
        rw [hc, htr v v.2 _ (hcl' _)]
      · by_cases hA : Over A l
        · exact hdec A hA v (Ine_le_Dec (F := ℚ) A hv) v.2
        · exact hI A hA v hv
      · exact hdec A hA v hv v.2
    have h0 : ∀ g : G ℚ Ω, g ∈ galOf ℚ K Ω → c g = 0 := fun g hg =>
      coprime_class_hom Ω K l hp.out hclass O (QO l O) htwo _ hX ⟨g,hg⟩ (hcl' g)
    funext g
    have swap := hc (δ*g) ((δ*g)⁻¹*(g*δ))
    rw [mul_inv_cancel_left, h0 _ (comm δ g), smul_zero, add_zero] at swap
    rw [hc g δ, hc δ g, hcδ, smul_zero, add_zero, zero_add] at swap
    apply (hun δ hδ).smul_eq_zero.1
    rw [sub_smul, one_smul, ← swap, sub_self]
  refine nonpos_iff_eq_zero.1 (shaToShT Ω l O α δ (hun δ hδ) l hp.out.ne_zero hin (fun A h h' => absurd h h') 0 fun a ha => ?_)
  have hnu : ¬ IsUnit (l : O) := fun h => by
    have := (dvrFacts l O).2.2.1
    rw [← map_natCast (algebraMap ℤ_[l] O), isUnit_map_iff] at h
    exact PadicInt.irreducible_p.not_isUnit h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a ∣ (l : O) ^ n := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hπ
    refine ⟨n, hn.dvd.trans (pow_dvd_pow_of_dvd ?_ n)⟩
    rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
    exact hnu
  have hall : ∀ n : ℕ, ∀ c ∈ ShT (QO l O) α δ l a, l ^ n • c = 0 → c = 0 := by
    intro n
    induction n with
    | zero => intro c _ h; simpa using h
    | succ n ih =>
      intro c hc h
      exact ih c hc (key a _ (nsmul_mem hc _) (by rw [smul_smul, ← pow_succ', h]))
  have : ShT (QO l O) α δ l a = ⊥ := by
    refine eq_bot_iff.2 fun c hc => hall n c hc (funext fun g => ?_)
    obtain ⟨y, hy⟩ := hn
    rw [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, hy, mul_comm, mul_smul, hc.2.2.1 g, smul_zero, Pi.zero_apply]
  rw [this]
  simp


#print axioms vanish_at_abelian_field
end RiemannReduction.CyclotomicLayer
