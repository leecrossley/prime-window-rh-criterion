import OrdinaryDyadicBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsQuadraticGaussSum

/-! The two quadratic characters used in the geometric window cut out the
radicals in Mizusawa's genus field over the full dyadic cyclotomic tower. -/

noncomputable section

open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base
  UpperTheory.V.Kum UpperTheory.V.Two

namespace RiemannReduction.Mizusawa

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

/-- Automorphisms fixing an element of the algebraic closure. -/
def fixes (x : Ω) : Subgroup (G ℚ Ω) where
  carrier := {g | g x = x}
  one_mem' := rfl
  mul_mem' {g h} hg hh := by change g (h x) = x; rw [hh, hg]
  inv_mem' {g} hg := by
    change g.symm x = x
    exact (g.symm_apply_eq.mpr hg.symm)

/-- The full dyadic cyclotomic tower with two specified radicals adjoined. -/
def radicalHost (a b : Ω) : Subgroup (G ℚ Ω) :=
  (fixes Ω a ⊓ fixes Ω b) ⊓ (cycZ ℚ Ω 2).ker

private theorem unit_square {p m : ℕ} [Fact p.Prime] (hm : m=p) (u : (ZMod m)ˣ)
    (a : ℕ) (ha : (u : ZMod m) = a) :
    u ∈ (powMonoidHom 2 : (ZMod m)ˣ →* (ZMod m)ˣ).range ↔ legendreSym p a = 1 := by
  subst m
  have hz : ((a : ℤ) : ZMod p) ≠ 0 := by rw [Int.cast_natCast, ← ha]; exact u.ne_zero
  rw [legendreSym.eq_one_iff p hz, Int.cast_natCast, ← ha, MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, by simp [pow_two]⟩
  · rintro ⟨r, hr⟩
    have nr : r ≠ 0 := by rintro rfl; simp at hr
    exact ⟨Units.mk0 r nr, Units.ext (by simpa [pow_two] using hr.symm)⟩

/-- The quadratic Gauss sum identifies the square subgroup of the mod-p
cyclotomic character with the stabilizer of either square root of -p. -/
theorem negative_radical {p : ℕ} (prime : p.Prime) (h4 : p % 4 = 3)
    (x : Ω) (hx : x ^ 2 = -(p : Ω)) : abU Ω (AbF.quad p) = fixes Ω x := by
  have hp : Fact p.Prime := ⟨prime⟩
  ext g
  change g ∈ abU Ω (AbF.quad p) ↔ g x = x
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨z,hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  let a := (galChar Ω p g : ZMod p).val
  have hstar : CF.pStar p = -(p : ℤ) := by
    have hodd : Odd (p/2) := Nat.odd_iff.mpr (by omega)
    rw [CF.pStar, hodd.neg_one_pow, neg_one_mul]
  have hroot : x ^ 2 = (CF.pStar p : ℤ) := by simpa [hstar] using hx
  have mul := ((CF.gauss Ω p z (by omega) hz).2 x hroot).2 g.toRingHom a (galChar_spec p g z hz.pow_eq_one)
  change g x = ((legendreSym p a : ℤ) : Ω) * x at mul
  have nx : x ≠ 0 := by
    rintro rfl
    simp [hp.out.ne_zero] at hx
  have hm : (AbF.quad p).m = p := max_eq_left hp.out.one_lt.le
  have val (m : ℕ) [NeZero m] (h : m = p) : (galChar Ω m g : ZMod m) = a := by
    subst m
    exact (ZMod.natCast_zmod_val _).symm
  change galChar Ω (AbF.quad p).m g ∈ (powMonoidHom 2 : (ZMod (AbF.quad p).m)ˣ →* _).range ↔ _
  rw [unit_square hm _ a (val _ hm)]
  constructor
  · intro sign
    simpa only [sign, Int.cast_one, one_mul] using mul
  · intro fixed
    have eq : ((legendreSym p a : ℤ) : Ω) * x = (1 : Ω) * x := by
      rw [← mul, one_mul]
      exact fixed
    exact_mod_cast mul_right_cancel₀ nx eq

/-- Over the dyadic tower positive and negative radicals define the same
quadratic extension, since the tower already fixes a square root of -1. -/
theorem host_eq_radicals {q d : ℕ} (hq : q.Prime) (hq8 : q % 8 = 3)
    (hd : d.Prime) (hd16 : d % 16 = 7) (a b : Ω) (ha : a ^ 2 = (q : Ω))
    (hb : b ^ 2 = (d : Ω)) :
    cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d)) = radicalHost Ω a b := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Ω) (by decide : 0 < 2)
  have ni : i ≠ 0 := by rintro rfl; simp at hi
  have hi4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hi]; norm_num
  have fix_i (g : G ℚ Ω) (hg : g ∈ (cycZ ℚ Ω 2).ker) : g i = i := by
    have h4 : galChar Ω 4 g = 1 := (levChar Ω 2 2 ⊤).2 hg
    rw [galChar_spec 4 g i hi4, h4]
    exact pow_one i
  have qneg := negative_radical Ω hq (by omega) (i*a) (by rw [mul_pow, hi, ha, neg_one_mul])
  have dneg := negative_radical Ω hd (by omega) (i*b) (by rw [mul_pow, hi, hb, neg_one_mul])
  have eq_base : cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d)) =
      (abU Ω (AbF.quad q) ⊓ abU Ω (AbF.quad d)) ⊓
      cycU 2 (abU Ω (withI (AbF.ofChar PChar.one))) := by
    ext g
    simp only [cycU, base2, (abBasic Ω).1, Subgroup.mem_inf]
    tauto
  rw [eq_base, RiemannReduction.GaussianTower.ordinary_tower, qneg, dneg]
  ext g
  change ((g (i*a) = i*a ∧ g (i*b) = i*b) ∧ g ∈ (⊤ : Subgroup (G ℚ Ω)) ∧ g ∈ _) ↔
    ((g a = a ∧ g b = b) ∧ g ∈ (cycZ ℚ Ω 2).ker)
  constructor
  · rintro ⟨⟨h₁, h₂⟩, _, hg⟩
    simp only [map_mul, fix_i g hg, mul_right_inj' ni] at h₁ h₂
    exact ⟨⟨h₁, h₂⟩, hg⟩
  · rintro ⟨⟨h₁, h₂⟩, hg⟩
    exact ⟨⟨by rw [map_mul, fix_i g hg, h₁], by rw [map_mul, fix_i g hg, h₂]⟩, trivial, hg⟩

end RiemannReduction.Mizusawa
