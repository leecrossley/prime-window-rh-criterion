import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IsAlgClosureRat
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LevChar

/-! The principal character has degree one. Its cyclotomic tower with the fourth
roots of unity adjoined is the pure dyadic tower over the rationals. -/
noncomputable section
open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Kum
  UpperTheory.V.Base UpperTheory.V.Two UpperTheory.V.Win

namespace RiemannReduction.GaussianTower

theorem ordinary_degree : (AbF.ofChar PChar.one).deg = 1 := by
  apply Subgroup.index_eq_one.mpr
  apply top_unique
  intro x _
  have hx : x = 1 := @Subsingleton.elim (ZMod 1)ˣ _ x 1
  rw [hx]
  exact (AbF.ofChar PChar.one).H.one_mem

theorem ordinary_tower (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] :
    cycU 2 (abU Ω (withI (AbF.ofChar PChar.one))) =
    cycU 2 (⊤ : Subgroup (G ℚ Ω)) := by
  obtain ⟨hsup, hdeg, _, hcyc⟩ := abBasic Ω
  have htop : abU Ω (AbF.ofChar PChar.one) = ⊤ :=
    Subgroup.index_eq_one.mp ((hdeg _).1.trans ordinary_degree)
  have h4 : (cycZ ℚ Ω 2).ker ≤ (galChar Ω 4).ker := (levChar Ω 2 2 ⊤).2
  simp only [cycU, withI, hsup, hcyc 4, htop, top_inf_eq, inf_eq_right.mpr h4]

def TwoInputAt (M : AbF) : Prop :=
  ∃ R : ℕ, ∀ q d : ℕ, PrimePair M.m q d →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L), TwoBase M q d L ∧ ABound 2 R L

end RiemannReduction.GaussianTower
