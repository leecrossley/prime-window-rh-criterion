import MizusawaHostField

/-! The real cyclotomic Z₂-extension is cut out by the dyadic cyclotomic
character modulo {±1}. Mizusawa writes the genus field using √(-qd). -/

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two

namespace RiemannReduction.Mizusawa

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

/-- The cyclotomic character modulo its order-two subgroup cuts out Q∞. -/
def realDyadic : Subgroup (G ℚ Ω) :=
  (powMonoidHom 2 : ℤ_[2]ˣ →* ℤ_[2]ˣ).ker.comap (cycZ ℚ Ω 2)

/-- Stabilizer of Q∞(a,b,c). For a²=q, b²=d and c²=-qd this is the
cyclotomic Z₂-extension of the genus field in Mizusawa's Lemma 4.2. -/
def genusHost (a b c : Ω) : Subgroup (G ℚ Ω) :=
  ((fixes Ω a ⊓ fixes Ω b) ⊓ fixes Ω c) ⊓ realDyadic Ω

omit [IsAlgClosure ℚ Ω] in
private theorem real_sign (g : G ℚ Ω) :
    g ∈ realDyadic Ω ↔ cycZ ℚ Ω 2 g = 1 ∨ cycZ ℚ Ω 2 g = -1 := by
  change (cycZ ℚ Ω 2 g) ^ 2 = 1 ↔ _
  simp only [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, Units.val_neg]
  exact sq_eq_one_iff

private theorem action_on_fourth_root (g : G ℚ Ω) (i : Ω) (hi : i ^ 2 = -1)
    (hg : cycZ ℚ Ω 2 g = -1) : g i = -i := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have (n : ℕ) : HasEnoughRootsOfUnity Ω (2 ^ n) := inferInstance
  have hi4 : i ^ (2 ^ 2) = 1 := by rw [show (2^2:ℕ) = 2*2 by decide, pow_mul, hi]; norm_num
  have act := cyclotomicCharacter.spec (L := Ω) 2 (n := 2) g.toRingEquiv i hi4
  change g i = i ^ ((PadicInt.toZModPow 2 (cycZ ℚ Ω 2 g : ℤ_[2])).val) at act
  simp only [hg, Units.val_neg, Units.val_one, map_neg, map_one] at act
  change g i = i ^ 3 at act
  rw [act, pow_succ, hi, neg_one_mul]

/-- Passing from the real tower and Mizusawa's three generators to the full
dyadic tower and the two positive radicals gives the very same Galois subgroup. -/
theorem radical_eq_genus {q d : ℕ} (hq : q.Prime) (hd : d.Prime) (a b c : Ω)
    (ha : a ^ 2 = (q : Ω)) (hb : b ^ 2 = (d : Ω)) (hc : c ^ 2 = -((q : Ω) * d)) :
    radicalHost Ω a b = genusHost Ω a b c := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Ω) (by decide : 0 < 2)
  have ni : i ≠ 0 := by rintro rfl; simp at hi
  have na : a ≠ 0 := by
    rintro rfl
    exact (Nat.cast_ne_zero.mpr hq.ne_zero : (q : Ω) ≠ 0) (by simpa using ha.symm)
  have nb : b ≠ 0 := by
    rintro rfl
    exact (Nat.cast_ne_zero.mpr hd.ne_zero : (d : Ω) ≠ 0) (by simpa using hb.symm)
  have roots : c = i*a*b ∨ c = -(i*a*b) := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [hc, mul_pow, mul_pow, hi, ha, hb]
    ring
  ext g
  have fix_product : g c = c ↔ g (i*a*b) = i*a*b := by
    rcases roots with h | h <;> simp [h]
  change ((g a = a ∧ g b = b) ∧ cycZ ℚ Ω 2 g = 1) ↔
    (((g a = a ∧ g b = b) ∧ g c = c) ∧ g ∈ realDyadic Ω)
  rw [fix_product, real_sign, map_mul, map_mul]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hg⟩
    have h4 : galChar Ω 4 g = 1 := (levChar Ω 2 2 ⊤).2 hg
    have hi4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hi]; norm_num
    have gi : g i = i := by rw [galChar_spec 4 g i hi4, h4]; exact pow_one i
    exact ⟨⟨⟨h₁, h₂⟩, by rw [gi, h₁, h₂]⟩, Or.inl hg⟩
  · rintro ⟨⟨⟨h₁, h₂⟩, hc'⟩, sign⟩
    refine ⟨⟨h₁, h₂⟩, sign.resolve_right ?_⟩
    intro minus
    have gi : g i = i := by
      simpa only [h₁, h₂, mul_left_inj' nb, mul_left_inj' na] using hc'
    have twice : (2 : Ω) * i = 0 := by
      have h := gi.symm.trans (action_on_fourth_root Ω g i hi minus)
      linear_combination h
    exact (mul_ne_zero (by norm_num) ni) twice

end RiemannReduction.Mizusawa
