import TameRayBound
import NineIntegralTower

/-! A three-generator upper bound on the ordinary host, obtained from global units. -/
noncomputable section
open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum
  UpperTheory.V.Two UpperTheory.V.Win
namespace RiemannReduction.TameSigns
open UnitSigns GaussianTower

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem finite_ray_eight {q d : ℕ} (hq : q.Prime) (q8 : q%8=3) (hd : d.Prime)
    (d16 : d%16=7) (j : ℕ) : RayRank Ω (galChar Ω (2^(j+4))).ker q d 3 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨z,hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2^(j+4))
  let K := IntermediateField.adjoin ℚ {z}
  have : IsCyclotomicExtension {2^(j+4)} ℚ K := by
    convert! (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin (2^(j+4)) ℚ Ω K hz).mpr rfl using 1
    exact Subsingleton.elim _ _
  have : NumberField K := IsCyclotomicExtension.numberField {2^(j+4)} ℚ K
  have : IsAlgClosure K Ω := isAlgClosure_top (F := ℚ) (L := K) (Ω := Ω)
  have : IsTotallyComplex K := IsCyclotomicExtension.Rat.isTotallyComplex K (n := 2^(j+4)) (by
    rw [pow_add]; have := Nat.two_pow_pos j; omega)
  exact finite_layer_bound K (Nat.mul_ne_zero hq.ne_zero hd.ne_zero) (fixed_layer hz)
    (sign_places (K := K) (j := j) hq q8 hd d16).some

/-- At most eight everywhere-unramified quadratic characters on the actual ordinary host. -/
theorem host_eight {q d : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d) :
    XRk 2 1 (cycU 2 (abU Ω (base2 (AbF.ofChar PChar.one) q d))) 3 := by
  apply host_rank_of_cofinal_finite_ray Ω (r := 1) pair
  intro start
  exact ⟨start+4,by omega,finite_ray_eight Ω pair.1 pair.2.1 pair.2.2.1 pair.2.2.2.1 start⟩

theorem host_tower_three {q d : ℕ} (pair : PrimePair (AbF.ofChar PChar.one).m q d)
    (L : Type) [Field L] [NumberField L] (field : IsAbField (base2 (AbF.ofChar PChar.one) q d) L) :
    Tower.GenLE ℤ_[2] (Tower.XX 2 L) 3 ∧ Tower.IsTower 2 L 3 := by
  have := isAlgClosure_rat L (AlgebraicClosure L)
  exact host_tower_of_rank (by decide) L field (host_eight (AlgebraicClosure L) pair)

theorem ordinary_three_input (bounds : TowerBound) : TwoInputAt (AbF.ofChar PChar.one) := by
  refine ⟨3,fun q d pair => ?_⟩
  obtain ⟨L,_,_,field⟩ := abExists (base2 (AbF.ofChar PChar.one) q d)
  exact ⟨L,inferInstance,inferInstance,twoBase _ q d pair L field,
    bounds 2 L 3 (host_tower_three pair L field).2⟩

#print axioms finite_ray_eight
#print axioms host_eight
#print axioms host_tower_three

end RiemannReduction.TameSigns
