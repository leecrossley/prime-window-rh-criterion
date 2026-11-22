import RaySignPlaces
import TameUnitRelations
import FiniteRayCharacter
import ReciprocityTheory.GaloisValuations.GlobalE
import ReciprocityTheory.GaloisValuations.GlobalEA
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-! The six finite primes as absolute tame sites of the cyclotomic layer. -/
noncomputable section
open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Hyp
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise
namespace RiemannReduction.TameSigns
open UnitSigns GaussianTower

theorem place_of_positive {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (x : 𝓞 K) (nx : x ≠ 0)
    (bad : A.valuation (algebraMap K Ω (x : K)) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver A w := by
  let I := (primeBelow (F := K) A).under (𝓞 K)
  have mem (y : 𝓞 K) : y ∈ I ↔ A.valuation (algebraMap K Ω (y : K)) < 1 := Iff.rfl
  have hn : I ≠ ⊥ := by intro e; have h := (mem x).mpr bad; rw [e,Ideal.mem_bot] at h; exact nx h
  exact ⟨⟨I,inferInstance,hn⟩,fun y => (mem y).symm⟩

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
variable (K : IntermediateField ℚ Ω) [NumberField K]

omit [IsAlgClosure ℚ Ω] in
theorem fix_inertia_iff (A : ValuationSubring Ω) (g : G K Ω) :
    (K.fixingSubgroupEquiv.symm g).1 ∈ Ine (F := ℚ) A ↔ g ∈ Ine (F := K) A := by
  change resGal ℚ K Ω g ∈ Ine (F := ℚ) A ↔ _
  constructor
  · intro h
    exact ⟨resGal_mem_Dec_iff.mp h.1,h.2⟩
  · intro h
    exact ⟨resGal_mem_Dec_iff.mpr h.1,h.2⟩

theorem fixed_layer {j : ℕ} {z : Ω} (root : IsPrimitiveRoot z (2^(j+4))) :
    (IntermediateField.adjoin ℚ {z}).fixingSubgroup = (galChar Ω (2^(j+4))).ker := by
  let E := IntermediateField.adjoin ℚ {z}
  have pos : 1 < 2^(j+4) := one_lt_pow₀ (by decide) (by omega)
  ext g
  constructor
  · intro hg
    have fix := (mem_fixingSubgroup_iff E g).mp hg z (subset_adjoin ℚ {z} (Set.mem_singleton z))
    apply Units.ext
    simpa using (galCharBasic Ω (2^(j+4))).2.2.1 g 1 z root (by simpa using fix)
  · intro hg
    have hg' : galChar Ω (2^(j+4)) g = 1 := hg
    have eq : g z = z := by
      rw [galChar_spec _ g z root.pow_eq_one,hg']
      have hv : (1 : ZMod (2^(j+4))).val = 1 := by
        simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (n := 2^(j+4)) pos
      rw [Units.val_one,hv,pow_one]
    apply (IntermediateField.le_iff_le (Subgroup.zpowers g) E).mp ?_ (Subgroup.mem_zpowers g)
    apply adjoin_simple_le_iff.mpr
    intro τ
    obtain ⟨τ,⟨a,rfl⟩⟩ := τ
    exact (MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer (G ℚ Ω) z).zpow_mem (show g ∈ MulAction.stabilizer (G ℚ Ω) z from eq) a))

theorem layer_sites {j q d : ℕ} (neq : q*d ≠ 0)
    (fieldEq : K.fixingSubgroup = (galChar Ω (2^(j+4))).ker) (S : SignPlaces K q d) :
    ∃ T : TameSites K.fixingSubgroup q d, ∀ i b, T.place i b = placeOf Ω (S.v (i,b)) := by
  have : IsAlgClosure K Ω := isAlgClosure_top (F := ℚ) (L := K) (Ω := Ω)
  let A := fun i b => placeOf Ω (S.v (i,b))
  have overAt (i b) : IsPlaceOver (A i b) (S.v (i,b)) := isPlaceOver_placeOf Ω _
  have odd (i b) : ¬ (A i b).valuation (2 : Ω) < 1 := by
    have h := (overAt i b) (2 : 𝓞 K)
    change (A i b).valuation (algebraMap K Ω (algebraMap (𝓞 K) K 2)) < 1 ↔ _ at h
    rw [map_ofNat,map_ofNat] at h
    exact S.odd (i,b) ∘ h.mp
  refine ⟨⟨A,odd,?_,?_⟩,fun _ _ => rfl⟩
  · intro i b
    rw [fieldEq]
    apply ineChar
    rw [Nat.cast_pow,Nat.cast_ofNat,map_pow]
    exact not_lt.mpr (one_le_pow₀ (le_of_not_gt (odd i b)))
  · intro B hB
    have hn : (↑(q*d) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr neq
    obtain ⟨W,hw⟩ := place_of_positive B (↑(q*d) : 𝓞 K) hn (by simpa using hB)
    have mem : (↑(q*d) : 𝓞 K) ∈ W.asIdeal := (hw _).mp (by simpa using hB)
    obtain ⟨t,ht⟩ := (S.covers W).mp mem
    obtain ⟨i,b⟩ := t
    subst W
    obtain ⟨g,hg⟩ := exists_smul_eq_of_isPlaceOver (F := K) (overAt i b) hw
    exact ⟨i,b,K.fixingSubgroupEquiv.symm g,hg⟩

end RiemannReduction.TameSigns
