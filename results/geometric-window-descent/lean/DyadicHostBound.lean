import OrdinaryDyadicBase
import RationalDyadicInertia

/-! A directly reusable bound for every admissible auxiliary host field. -/
noncomputable section
open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.Two

namespace RiemannReduction.GaussianTower

theorem host_rank_twenty_four (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {q d : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d) :
    XRk 2 1 (cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d))) 24 := by
  have trivial : XRk 2 1 (cycU 2 (abU Ω (withI (AbF.ofChar PChar.one)))) 0 := by
    rw [ordinary_tower]
    exact pure_rank_zero Ω
  have bound := baseRk Ω (AbF.ofChar PChar.one) q d 0 pair trivial
  rw [ordinary_degree] at bound
  exact bound

theorem host_tower_twenty_four {q d : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d)
    (L : Type) [Field L] [NumberField L]
    (field : IsAbField (base2 (AbF.ofChar PChar.one) q d) L) :
    Tower.GenLE ℤ_[2] (Tower.XX 2 L) 24 ∧ Tower.IsTower 2 L 24 := by
  have := isAlgClosure_rat L (AlgebraicClosure L)
  have rank := host_rank_twenty_four (AlgebraicClosure L) pair
  have roots := hasMuQ.2.2 (AbF.ofChar PChar.one) q d L field
  exact ⟨genLE_of_abRk 1 L field rank, complex_of_root (by norm_num) roots, roots,
    by decide, genLE_of_abRk 2 L field rank⟩

#print axioms host_rank_twenty_four
#print axioms host_tower_twenty_four
end RiemannReduction.GaussianTower
