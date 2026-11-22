import GroundTheory.GlobalFields.GlobalReciprocity.General

/-! A global unit gives a parity relation on the finite ramified places of
an abelian extension of a totally imaginary number field. -/
noncomputable section
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.SemiLocal
open scoped BigOperators

namespace RiemannReduction.UnitParity

variable (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K]
  [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

attribute [local instance] GroundTheory.Global.galCommGroup

private theorem finite_symbol_parity (u : Kˣ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (outside : ∀ v ∉ S, localSymbol L v (finiteProj v (diagonal K u)) = 1)
    (χ : (L ≃ₐ[K] L) →* Multiplicative (ZMod 2)) :
    (∑ v ∈ S, (χ (localSymbol L v (finiteProj v (diagonal K u)))).toAdd) = 0 := by
  classical
  have global := ideleSymbol_diagonal (L := L) u
  rw [ideleSymbol_apply] at global
  have arch (w : InfinitePlace K) :
      infiniteLocalSymbol L w (infiniteProj w (diagonal K u)) = 1 := by
    rw [infiniteLocalSymbol_of_not_isReal L w
      (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))]
    rfl
  simp only [arch, Finset.prod_const_one, mul_one] at global
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (fun v hv => by
    by_contra h
    exact hv (outside v h))] at global
  have image := congrArg χ global
  rw [map_prod, map_one] at image
  simpa using congrArg Multiplicative.toAdd image

/-- If the extension is unramified outside S, a global integral unit
automatically has trivial symbol at every other finite place. -/
theorem global_unit_parity (u : (𝓞 K)ˣ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (unramified : ∀ v ∉ S, ∃ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    (χ : (L ≃ₐ[K] L) →* Multiplicative (ZMod 2)) :
    (∑ v ∈ S, (χ (localSymbol L v (finiteProj v
      (diagonal K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u))))).toAdd) = 0 := by
  apply finite_symbol_parity K L
  intro v hv
  obtain ⟨w, hw⟩ := unramified v hv
  apply units_le_ker_localSymbol L v w hw
  rw [Submonoid.mem_units_iff, ← map_inv, ← map_inv, ← map_inv,
    coe_finiteProj_diagonal, coe_finiteProj_diagonal]
  exact ⟨HeightOneSpectrum.coe_algebraMap_mem (𝓞 K) K v (u : 𝓞 K),
    HeightOneSpectrum.coe_algebraMap_mem (𝓞 K) K v (↑u⁻¹ : 𝓞 K)⟩

#print axioms global_unit_parity

end RiemannReduction.UnitParity
