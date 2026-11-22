import FiniteTameParity
import RayLayerSites

/-! Identifying the finite Artin symbol with the value of a ray character on the
chosen absolute tame generator, using the field cut out by its open kernel. -/
noncomputable section
open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  ReciprocityTheory.Hyp Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base
  UpperTheory.V.Kum UpperTheory.V.Two GroundTheory.Global GroundTheory.Global.SemiLocal
open scoped Pointwise
namespace RiemannReduction.TameSigns
open UnitSigns GaussianTower

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
variable (K : IntermediateField ℚ Ω) [NumberField K] [IsAlgClosure K Ω] {q d : ℕ}
private abbrev Ray := CharOff K.fixingSubgroup (ineOff ℚ Ω (q*d)) 2

private def pull (χ : Ray K (q := q) (d := d)) : G K Ω →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (χ.1 (K.fixingSubgroupEquiv.symm g))
  map_one' := by
    change χ.1 (K.fixingSubgroupEquiv.symm 1) = 0
    rw [map_one]
    have h := χ.2.2.1 1 1
    rw [one_mul] at h
    linear_combination -h
  map_mul' x y := by
    change χ.1 (K.fixingSubgroupEquiv.symm (x*y)) = _
    rw [map_mul]
    exact χ.2.2.1 _ _

omit [NumberField K] [IsAlgClosure K Ω] in
private theorem pull_locally_constant (χ : Ray K (q := q) (d := d)) : IsLocallyConstant (pull K χ) := by
  have c : Continuous (fun g : G K Ω => K.fixingSubgroupEquiv.symm g) :=
    Continuous.subtype_mk (continuous_resGal (F := ℚ) (L := K) (Ω := Ω)) _
  exact (χ.2.1.comp_continuous c).comp Multiplicative.ofAdd

omit [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] in
private theorem over_nat {E : Type} [Field E] [NumberField E] [Algebra E Ω]
    (A : ValuationSubring Ω) (W : HeightOneSpectrum (𝓞 E)) (hw : IsPlaceOver A W) (n : ℕ) :
    A.valuation (n : Ω) < 1 ↔ (n : 𝓞 E) ∈ W.asIdeal := by
  have h := hw (n : 𝓞 E)
  change A.valuation (algebraMap E Ω (algebraMap (𝓞 E) E (n : 𝓞 E))) < 1 ↔ _ at h
  simpa only [map_natCast] using h

omit [IsAlgClosure ℚ Ω] [NumberField K] [IsAlgClosure K Ω] in
private theorem under_over {L : IntermediateField K Ω} [NumberField L]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 K)) := by
  intro x
  rw [IsScalarTower.algebraMap_apply K L Ω]
  exact h (algebraMap (𝓞 K) (𝓞 L) x)

private theorem unit_relations [IsTotallyComplex K] (nz : q*d ≠ 0)
    (S : SignPlaces K q d) (T : TameSites K.fixingSubgroup q d)
    (sites : ∀ i b, T.place i b = placeOf Ω (S.v (i,b))) : T.UnitRelations := by
  intro χ
  obtain ⟨L,hfin,hgal,ψ,inject,rep⟩ := finite_character (pull K χ) (pull_locally_constant K χ)
  let : NumberField L := NumberField.of_module_finite K L
  let : IsAlgClosure L Ω := isAlgClosure_top (F := K) (L := L) (Ω := Ω)
  have : IsMulCommutative Gal(L/K) := ⟨⟨fun x y => inject (by rw [map_mul,map_mul,mul_comm])⟩⟩
  have expTwo (g : Gal(L/K)) : g^2=1 := by
    apply inject
    rw [map_pow,map_one]
    exact (show ∀ x : Multiplicative (ZMod 2), x^2=1 by decide) _
  have unram (v : HeightOneSpectrum (𝓞 K)) (outside : (↑(q*d) : 𝓞 K) ∉ v.asIdeal) :
      ∃ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    obtain ⟨w⟩ := nonempty_placesOver L v
    let A := placeOf Ω w.1
    have hw : IsPlaceOver A w.1 := isPlaceOver_placeOf Ω w.1
    have base := under_over K A w.1 hw
    have e : w.1.under (𝓞 K) = v := HeightOneSpectrum.ext w.2.over.symm
    rw [e] at base
    have away := outside ∘ (over_nat A v base (q*d)).mp
    have trivial : w.1.asIdeal.inertia Gal(L/K) = ⊥ := (absolute_inertia_iff ψ inject A w.1 hw).mp (by
      intro g hg
      rw [rep]
      exact congrArg Multiplicative.ofAdd (χ.2.2.2 (K.fixingSubgroupEquiv.symm g)
        ⟨A,away,(fix_inertia_iff K A g).mpr hg⟩))
    refine ⟨w,?_⟩
    rw [← natCard_inertia v w.1,Subgroup.card_eq_one]
    exact trivial
  have symbol_eq (i b) : T.value χ i b = symbolValue ψ (S.v (i,b)) S.z := by
    let v := S.v (i,b)
    let A := T.place i b
    have ha : IsPlaceOver A v := by change IsPlaceOver (T.place i b) v; rw [sites]; exact isPlaceOver_placeOf Ω v
    have hv : (↑(q*d) : 𝓞 K) ∈ v.asIdeal := (S.covers v).mpr ⟨(i,b),rfl⟩
    have pos := (over_nat A v ha (q*d)).mpr hv
    obtain ⟨w,hw⟩ := place_of_positive (K := L) A (↑(q*d) : 𝓞 L) (Nat.cast_ne_zero.mpr nz) (by
      change A.valuation (algebraMap L Ω (algebraMap (𝓞 L) L (↑(q*d) : 𝓞 L))) < 1
      simpa only [map_natCast] using pos)
    have underEq := eq_of_isPlaceOver (under_over K A w hw) ha
    have : w.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal underEq).symm⟩
    have absEq : T.value χ i b = 0 ↔ w.asIdeal.inertia Gal(L/K) = ⊥ := by
      rw [T.value_zero_iff,← absolute_inertia_iff ψ inject A w hw]
      constructor
      · intro h g hg
        rw [rep]
        exact congrArg Multiplicative.ofAdd (h ⟨_,(fix_inertia_iff K A g).mpr hg⟩)
      · intro h g
        let a : K.fixingSubgroup := ⟨g.1,T.inside i b g.2⟩
        let k := K.fixingSubgroupEquiv a
        have mem : k ∈ Ine (F := K) A := (fix_inertia_iff K A k).mp (by
          change (K.fixingSubgroupEquiv.symm (K.fixingSubgroupEquiv a)).1 ∈ _
          rw [K.fixingSubgroupEquiv.symm_apply_apply]
          exact g.2)
        have h' := h k mem
        rw [rep] at h'
        change χ.1 (K.fixingSubgroupEquiv.symm (K.fixingSubgroupEquiv a)) = 0 at h'
        rwa [K.fixingSubgroupEquiv.symm_apply_apply] at h'
    have symEq := detects_finite_inertia (K := K) (L := L) v w expTwo (two_ne_zero K v (S.odd _)) S.z (S.root _)
    apply (show ∀ a b : ZMod 2, (a=0 ↔ b=0) → a=b by decide)
    exact absEq.trans (symEq.symm.trans ⟨fun h => congrArg Multiplicative.toAdd (by rw [h,map_one] : ψ _ = 1),
      fun h => inject (h.trans ψ.map_one.symm)⟩)
  have eqPair (i : Fin 3) : T.pairSum χ i = 0 := by
    unfold TameSites.pairSum
    rw [symbol_eq,symbol_eq,finite_pair_equal S ψ unram i]
    exact (show ∀ x : ZMod 2, x+x=0 by decide) _
  simp only [eqPair,add_zero,and_self]

theorem finite_layer_bound [IsTotallyComplex K] (nz : q*d ≠ 0) {j : ℕ}
    (fieldEq : K.fixingSubgroup = (galChar Ω (2^(j+4))).ker) (S : SignPlaces K q d) :
    RayRank Ω (galChar Ω (2^(j+4))).ker q d 3 := by
  obtain ⟨T,sites⟩ := layer_sites K nz fieldEq S
  have bound := T.ray_rank_three (V := K.fixingSubgroup)
    (fieldEq ▸ pure_layer_one Ω (show 0 < j+4 by omega)) (unit_relations K nz S T sites)
  rwa [fieldEq] at bound

end RiemannReduction.TameSigns
