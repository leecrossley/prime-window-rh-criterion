import OrdinaryDyadicBase
import RationalDyadicInertia

noncomputable section
open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Kum
  UpperTheory.V.Base UpperTheory.V.Two UpperTheory.V.Win

namespace RiemannReduction.GaussianTower

theorem ordinary_two_input_unconditional (bounds : TowerBound) :
    TwoInputAt (AbF.ofChar PChar.one) := by
  let M := AbF.ofChar PChar.one
  refine ⟨24, fun q d pair => ?_⟩
  obtain ⟨L, _, _, hL⟩ := abExists (base2 M q d)
  have := isAlgClosure_rat L (AlgebraicClosure L)
  have rank0 : XRk 2 1 (cycU 2 (abU (AlgebraicClosure L) (withI M))) 0 := by
    rw [ordinary_tower]
    exact pure_rank_zero _
  have rank := baseRk (AlgebraicClosure L) M q d 0 pair rank0
  have deg : M.deg = 1 := ordinary_degree
  rw [deg] at rank
  have roots := hasMuQ.2.2 M q d L hL
  have tower : Tower.IsTower 2 L 24 :=
    ⟨complex_of_root (by norm_num) roots, roots, by decide, genLE_of_abRk 2 L hL rank⟩
  exact ⟨L, inferInstance, inferInstance, twoBase M q d pair L hL, bounds 2 L 24 tower⟩

#print axioms ordinary_two_input_unconditional
end RiemannReduction.GaussianTower
