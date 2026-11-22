import OrdinaryRayDescent

noncomputable section
open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum
  UpperTheory.V.Two UpperTheory.V.Win
namespace RiemannReduction.GaussianTower

theorem host_tower_of_rank {q d r : ℕ} (pos : 1 ≤ r)
    (L : Type) [Field L] [NumberField L] [IsAlgClosure ℚ (AlgebraicClosure L)] (field : IsAbField (base2 (AbF.ofChar PChar.one) q d) L)
    (rank : XRk 2 1 (cycU 2 (abU (AlgebraicClosure L) (base2 (AbF.ofChar PChar.one) q d))) r) :
    Tower.GenLE ℤ_[2] (Tower.XX 2 L) r ∧ Tower.IsTower 2 L r := by
  have roots := hasMuQ.2.2 (AbF.ofChar PChar.one) q d L field
  exact ⟨genLE_of_abRk 1 L field rank,complex_of_root (by norm_num) roots,roots,pos,
    genLE_of_abRk 2 L field rank⟩

theorem host_tower_nine {q d : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d)
    (L : Type) [Field L] [NumberField L] (field : IsAbField (base2 (AbF.ofChar PChar.one) q d) L) :
    Tower.GenLE ℤ_[2] (Tower.XX 2 L) 9 ∧ Tower.IsTower 2 L 9 := by
  have := isAlgClosure_rat L (AlgebraicClosure L)
  exact host_tower_of_rank (by decide) L field (host_rank_nine (AlgebraicClosure L) pair)

theorem ordinary_nine_input (bounds : TowerBound) : TwoInputAt (AbF.ofChar PChar.one) := by
  refine ⟨9,fun q d pair => ?_⟩
  obtain ⟨L,_,_,field⟩ := abExists (base2 (AbF.ofChar PChar.one) q d)
  exact ⟨L,inferInstance,inferInstance,twoBase _ q d pair L field,
    bounds 2 L 9 (host_tower_nine pair L field).2⟩

#print axioms host_tower_nine
#print axioms ordinary_nine_input
end RiemannReduction.GaussianTower
