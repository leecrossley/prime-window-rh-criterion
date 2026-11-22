import RaySignPlaces
import LocalTameUnitSigns

/-! The three relations on the actual finite local Artin symbols. -/
noncomputable section
open NumberField IsDedekindDomain ValuativeRel GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped WithZero
namespace RiemannReduction.TameSigns
open UnitSigns

theorem two_ne_zero (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (h : (2 : 𝓞 K) ∉ v.asIdeal) : (2 : 𝓀[v.adicCompletion K]) ≠ 0 := by
  intro zero
  have eq : (residueEquivInteger v) (Ideal.Quotient.mk v.asIdeal (2 : 𝓞 K)) = 0 := by
    rw [map_ofNat,map_ofNat]
    exact zero
  exact h (Ideal.Quotient.eq_zero_iff_mem.mp ((residueEquivInteger v).injective (eq.trans (map_zero _).symm)))

def symbolValue {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
    (χ : Gal(L/K) →* Multiplicative (ZMod 2)) (v : HeightOneSpectrum (𝓞 K)) (u : (𝓞 K)ˣ) : ZMod 2 :=
  (χ (localSymbol L v (finiteProj v (diagonal K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u))))).toAdd

/-- The only possible finite inertia patterns have equal coordinates within each pair. -/
theorem finite_pair_equal {K L : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
    {q d : ℕ} (S : SignPlaces K q d) (χ : Gal(L/K) →* Multiplicative (ZMod 2))
    (unram : ∀ v, (↑(q*d) : 𝓞 K) ∉ v.asIdeal →
      ∃ w : GroundTheory.Global.SemiLocal.PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    ∀ i : Fin 3, symbolValue χ (S.v (i,false)) S.z = symbolValue χ (S.v (i,true)) S.z := by
  classical
  let f := fun t => symbolValue χ (S.v t) S.z
  have sum (u : (𝓞 K)ˣ) : ∑ t : Sites, symbolValue χ (S.v t) u = 0 := by
    have h := UnitParity.global_unit_parity K L u (Finset.univ.image S.v) (fun v notin =>
      unram v (fun bad => by obtain ⟨t,ht⟩ := (S.covers v).mp bad; exact notin (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,ht⟩))) χ
    rw [Finset.sum_image (fun _ _ _ _ h => S.inj h)] at h
    exact h
  have formula (u : (𝓞 K)ˣ) (t : Sites) : symbolValue χ (S.v t) u =
      if squareAt (S.v t).asIdeal (u : 𝓞 K) then 0 else f t := by
    have h := local_artin_values (S.v t) u S.z (two_ne_zero K _ (S.odd t)) (S.root t) χ
      (fun g => by apply Multiplicative.toAdd.injective; exact (show ∀ a : ZMod 2, (2:ℕ) • a = 0 by decide) (χ g).toAdd)
    split
    · next sq => exact congrArg Multiplicative.toAdd (h.1 sq)
    · next ns => exact congrArg Multiplicative.toAdd (h.2 ns)
  have z := sum S.z
  have u := sum S.u
  have c := sum S.c
  change ∑ t : Sites, f t = 0 at z
  simp only [fun t => formula S.u t,S.first] at u
  simp only [fun t => formula S.c t,S.second] at c
  simp only [Sites,Fintype.sum_prod_type,Fin.sum_univ_three,Fintype.sum_bool] at z u c
  simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide,if_false,if_true,add_zero] at u c
  have pair (i : Fin 3) : f (i,false)+f (i,true) = 0 := by
    fin_cases i
    · change f (0,false)+f (0,true)=0
      linear_combination u + c - z
    · change f (1,false)+f (1,true)=0
      linear_combination z - c
    · change f (2,false)+f (2,true)=0
      linear_combination z - u
  intro i
  have h := pair i
  change f (i,false) = f (i,true)
  exact (show ∀ a b : ZMod 2, a+b=0 → a=b by decide) _ _ h

end RiemannReduction.TameSigns
