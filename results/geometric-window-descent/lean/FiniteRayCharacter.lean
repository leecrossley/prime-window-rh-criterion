import LocalTameUnitSigns
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

/-! Finite realisation of a locally constant quadratic character and its inertia. -/
noncomputable section
open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  UpperTheory.V.Kum UpperTheory.V.CF
namespace RiemannReduction.TameSigns

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

theorem finite_character (f : G K Ω →* Multiplicative (ZMod 2)) (lc : IsLocallyConstant f) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsGalois K L)
      (ψ : Gal(L/K) →* Multiplicative (ZMod 2)), Function.Injective ψ ∧
      ∀ g, ψ (resTo K L Ω g) = f g := by
  let H : ClosedSubgroup (G K Ω) := ⟨f.ker, lc.isClosed_fiber 1⟩
  let L := fixedField f.ker
  have : H.Normal := (inferInstance : f.ker.Normal)
  have : IsGalois K Ω := inferInstance
  have fix : L.fixingSubgroup = f.ker := InfiniteGalois.fixingSubgroup_fixedField H
  have openFix : IsOpen (L.fixingSubgroup : Set (G K Ω)) := fix ▸ lc.isOpen_fiber 1
  have fin : FiniteDimensional K L := (InfiniteGalois.isOpen_iff_finite L).mp openFix
  let e := InfiniteGalois.normalAutEquivQuotient H
  let ψ := (QuotientGroup.kerLift f).comp e.symm.toMonoidHom
  refine ⟨L,fin,inferInstance,ψ,(QuotientGroup.kerLift_injective f).comp e.symm.injective,?_⟩
  intro g
  change QuotientGroup.kerLift f (e.symm (e (QuotientGroup.mk g))) = f g
  rw [e.symm_apply_apply,QuotientGroup.kerLift_mk]

/-- An absolute quadratic character vanishes on the inertia of a prolongation
exactly when the finite inertia of its faithful realisation is trivial. -/
theorem absolute_inertia_iff {L : IntermediateField K Ω} [FiniteDimensional K L] [NumberField L]
    [IsGalois K L] (ψ : Gal(L/K) →* Multiplicative (ZMod 2)) (faithful : Function.Injective ψ)
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)) (above : IsPlaceOver A w) :
    (∀ g ∈ Ine (F := K) A, ψ (resTo K L Ω g) = 1) ↔ w.asIdeal.inertia Gal(L/K) = ⊥ := by
  rw [← ineAbs K L Ω A w above]
  constructor
  · intro h
    apply eq_bot_iff.mpr
    rintro _ ⟨g,hg,rfl⟩
    exact faithful ((h g hg).trans ψ.map_one.symm)
  · intro h g hg
    have mem : resTo K L Ω g ∈ (Ine (F := K) A).map (resTo K L Ω) := ⟨g,hg,rfl⟩
    rw [h,Subgroup.mem_bot] at mem
    rw [mem,map_one]

end RiemannReduction.TameSigns
