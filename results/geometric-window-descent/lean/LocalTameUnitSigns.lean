import GroundTheory.GlobalFields.ClassFieldConsequences.ConductorLocal
import GroundTheory.GlobalFields.CompletionAtPlace.Degree
import MizusawaUnitParity

/-! The square class of a global unit determines its local quadratic Artin symbol
at an odd place. A nonsquare detects ramification in any elementary 2-extension. -/
noncomputable section
open NumberField IsDedekindDomain ValuativeRel GroundTheory.LocalField GroundTheory.Global
  GroundTheory.Global.IdeleGroup
open scoped WithZero
namespace RiemannReduction.TameSigns

section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem square_lift (odd : (2 : 𝓀[k]) ≠ 0) {u : 𝒪[k]ˣ}
    (square : IsSquare ((unitsToResidue k u : 𝓀[k]ˣ) : 𝓀[k])) : IsSquare u := by
  obtain ⟨x,hx⟩ := square
  have nz : x ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨y,hy⟩ := unitsToResidue_surjective k (Units.mk0 x nz)
  have res : unitsToResidue k u = unitsToResidue k (y^2) := by
    rw [map_pow,hy]
    exact Units.ext (by simpa only [Units.val_pow_eq_pow_val,Units.val_mk0,pow_two,Units.val_mul] using hx)
  have mem : u/(y^2) ∈ unitFiltration k 1 := by
    rw [← ker_unitsToResidue,MonoidHom.mem_ker,map_div,res,div_self' ]
  obtain ⟨t,ht⟩ := unitFiltration_one_le_range_pow odd mem
  change t^2 = u/y^2 at ht
  refine ⟨t*y,?_⟩
  calc
    u = (u/y^2)*y^2 := (div_mul_cancel _ _).symm
    _ = (t*y)*(t*y) := by rw [← ht,pow_two,pow_two]; ac_rfl

/-- Any homomorphism of exponent two on the local units takes a single
value on nonsquare residues and is trivial on square residues. -/
theorem on_units {A : Type*} [Group A] (f : 𝒪[k]ˣ →* A)
    (two : ∀ a, f a ^ 2 = 1) (odd : (2 : 𝓀[k]) ≠ 0) (u z : 𝒪[k]ˣ)
    (ns : ¬ IsSquare ((unitsToResidue k z : 𝓀[k]ˣ) : 𝓀[k])) :
    (IsSquare ((unitsToResidue k u : 𝓀[k]ˣ) : 𝓀[k]) → f u = 1) ∧
    (¬ IsSquare ((unitsToResidue k u : 𝓀[k]ˣ) : 𝓀[k]) → f u = f z) := by
  classical
  let := Fintype.ofFinite 𝓀[k]
  have trivial {x : 𝒪[k]ˣ} (square : IsSquare ((unitsToResidue k x : 𝓀[k]ˣ) : 𝓀[k])) :
      f x = 1 := by
    obtain ⟨y,hy⟩ := square_lift odd square
    rw [hy,map_mul,← pow_two,two]
  refine ⟨trivial, fun hu => ?_⟩
  have sign := (quadraticChar_neg_one_iff_not_isSquare.mpr hu)
  have refSign := (quadraticChar_neg_one_iff_not_isSquare.mpr ns)
  have s : IsSquare ((unitsToResidue k (u*z) : 𝓀[k]ˣ) : 𝓀[k]) := by
    apply (quadraticChar_one_iff_isSquare (unitsToResidue k (u*z)).ne_zero).mp
    rw [map_mul,Units.val_mul,map_mul,sign,refSign]; decide
  have both := trivial s
  rw [map_mul] at both
  calc f u = f u * (f z * f z) := by rw [← pow_two,two,mul_one]
       _ = f z := by rw [← mul_assoc,both,one_mul]
end Local

section Global
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
attribute [local instance] GroundTheory.Global.galCommGroup

def localUnit (v : HeightOneSpectrum (𝓞 K)) (u : (𝓞 K)ˣ) : 𝒪[v.adicCompletion K]ˣ :=
  Units.map (ringOfIntegersToInteger v).toMonoidHom u

private theorem local_square_iff (v : HeightOneSpectrum (𝓞 K)) (u : (𝓞 K)ˣ) :
    IsSquare ((unitsToResidue (v.adicCompletion K) (localUnit v u) : _) : 𝓀[v.adicCompletion K]) ↔
      IsSquare (Ideal.Quotient.mk v.asIdeal (u : 𝓞 K)) := by
  let e := residueEquivInteger v
  change IsSquare (e (Ideal.Quotient.mk v.asIdeal (u : 𝓞 K))) ↔ _
  refine ⟨?_,fun h => h.map e⟩
  rintro ⟨a,ha⟩
  exact ⟨e.symm a,by rw [← map_mul,← ha,e.symm_apply_apply]⟩

/-- The local Artin symbols of integral units, tested by an arbitrary quadratic character. -/
theorem local_artin_values (v : HeightOneSpectrum (𝓞 K)) (u z : (𝓞 K)ˣ)
    (odd : (2 : 𝓀[v.adicCompletion K]) ≠ 0)
    (ns : ¬ IsSquare (Ideal.Quotient.mk v.asIdeal (z : 𝓞 K)))
    {A : Type*} [Group A] (χ : Gal(L/K) →* A) (two : ∀ g, χ g ^ 2 = 1) :
    let symbol := fun x : (𝓞 K)ˣ => χ (localSymbol L v (finiteProj v
      (diagonal K (Units.map (algebraMap (𝓞 K) K).toMonoidHom x))))
    (IsSquare (Ideal.Quotient.mk v.asIdeal (u : 𝓞 K)) → symbol u = 1) ∧
    (¬ IsSquare (Ideal.Quotient.mk v.asIdeal (u : 𝓞 K)) → symbol u = symbol z) := by
  let f := (χ.comp (localSymbol L v)).comp (unitsIncl (v.adicCompletion K))
  have h := on_units f (fun a => two _) odd (localUnit v u) (localUnit v z)
    (ns ∘ (local_square_iff v z).mp)
  rw [local_square_iff] at h
  exact h

/-- A nonsquare global unit has trivial local Artin symbol exactly when
the finite elementary 2-extension has trivial inertia at that place. -/
theorem detects_finite_inertia (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (two : ∀ g : Gal(L/K), g^2 = 1) (odd : (2 : 𝓀[v.adicCompletion K]) ≠ 0)
    (z : (𝓞 K)ˣ) (ns : ¬ IsSquare (Ideal.Quotient.mk v.asIdeal (z : 𝓞 K))) :
    localSymbol L v (finiteProj v (diagonal K (Units.map (algebraMap (𝓞 K) K).toMonoidHom z))) = 1 ↔
      w.asIdeal.inertia Gal(L/K) = ⊥ := by
  rw [← Subgroup.card_eq_one, natCard_inertia v w]
  let f := (localSymbol L v).comp (unitsIncl (v.adicCompletion K))
  constructor
  · intro hz
    apply ramificationIdx_eq_one_of_units_le_ker_localSymbol v _ w
    rintro _ ⟨a,_,rfl⟩
    have h := on_units f (fun a => two _) odd a (localUnit v z) (ns ∘ (local_square_iff v z).mp)
    by_cases square : IsSquare ((unitsToResidue (v.adicCompletion K) a : _) : 𝓀[v.adicCompletion K])
    · exact h.1 square
    · exact (h.2 square).trans hz
  · intro he
    apply units_le_ker_localSymbol L v ⟨w,inferInstance⟩ he
    rw [Submonoid.mem_units_iff, ← map_inv, ← map_inv, ← map_inv,
      coe_finiteProj_diagonal,coe_finiteProj_diagonal]
    exact ⟨HeightOneSpectrum.coe_algebraMap_mem (𝓞 K) K v (z : 𝓞 K),
      HeightOneSpectrum.coe_algebraMap_mem (𝓞 K) K v (↑z⁻¹ : 𝓞 K)⟩

end Global
end RiemannReduction.TameSigns
