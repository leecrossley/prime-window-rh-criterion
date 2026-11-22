import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LevGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts

/-! The fields at different conductor-one pages form a tower inside a common algebraic closure. -/

noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.HC
open UpperTheory.V UpperTheory.V.HV UpperTheory.V.Base UpperTheory.Top

namespace RiemannReduction.ConductorOne

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem reduce_cls {m n : ℕ} [NeZero m] [NeZero n] (d : m ∣ n) (g : G ℚ Ω) :
    ZMod.unitsMap d (Chr.cls ℚ Ω n g) = Chr.cls ℚ Ω m g :=
  DFunLike.congr_fun ((Chr.clsFacts ℚ Ω n).2.1 m d) g

private theorem field_conditions (h : UpperTheory.V.HV.Host) [NeZero h.q1] [NeZero h.d]
    [NeZero h.q] (g : G ℚ Ω) :
    g ∈ Chr.levH ℚ Ω h.H ↔
      ((Chr.cls ℚ Ω (2 ^ (h.ex + 2)) g ∈ Subgroup.zpowers (-1) ∧
        Chr.cls ℚ Ω h.q g ∈ h.chi.χ.toUnitHom.ker) ∧
       Chr.cls ℚ Ω h.q1 g ∈ (powMonoidHom 2).range) ∧
       Chr.cls ℚ Ω h.d g ∈ (powMonoidHom 2).range := by
  simp only [Chr.levH, UpperTheory.V.HV.Host.H, Subgroup.mem_comap, Subgroup.mem_inf, reduce_cls]

private theorem neg_one_restrict {m n : ℕ} (h : m ∣ n) (v : (ZMod n)ˣ)
    (hs : v ∈ Subgroup.zpowers (-1)) : ZMod.unitsMap h v ∈ Subgroup.zpowers (-1) := by
  obtain ⟨j, rfl⟩ := hs
  refine ⟨j, ?_⟩
  rw [map_zpow]
  apply Units.ext
  simp [ZMod.unitsMap]

private theorem cls_at_two {g : G ℚ Ω} (h : cycZ ℚ Ω 2 g = 1) (n : ℕ) :
    Chr.cls ℚ Ω (2^n) g = 1 := by
  let _ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have key := cyclotomicCharacter.toZModPow (L := Ω) 2 (n := n)
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)
  apply Units.ext
  change (modularCyclotomicCharacter Ω (Chr.card_roots ℚ Ω (2^n))
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)).val = 1
  rw [← key]
  change PadicInt.toZModPow n ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2]) = 1
  rw [h, Units.val_one, map_one]

/-- All three structural inputs needed to descend Sha are consequences of the
    defining fields at the two pages. In particular the auxiliary pair is fixed. -/
theorem principal_field_tower {q d i j : ℕ} (hp : PrimePair 1 q d) (hi : 2 ≤ i) (hij : i ≤ j)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F Ω] [Algebra E Ω]
    (lf : IsChiField PChar.one i q d F) (uf : IsChiField PChar.one j q d E) :
    IsAbelianGalois ℚ E ∧ galOf ℚ E Ω ≤ galOf ℚ F Ω ∧
      cycU 2 (galOf ℚ F Ω) ≤ galOf ℚ E Ω ∧
      ∃ v : ℕ, (galOf ℚ E Ω).relIndex (galOf ℚ F Ω) = 2^v := by
  let low : UpperTheory.V.HV.Host := ⟨PChar.one, i, q, d, hi, hp⟩
  let high : UpperTheory.V.HV.Host := ⟨PChar.one, j, q, d, hi.trans hij, hp⟩
  let _ : NeZero q := ⟨hp.1.ne_zero⟩
  let _ : NeZero d := ⟨hp.2.2.1.ne_zero⟩
  let _ : NeZero low.q1 := inferInstanceAs (NeZero q)
  let _ : NeZero low.d := inferInstanceAs (NeZero d)
  let _ : NeZero low.q := inferInstanceAs (NeZero 1)
  let _ : NeZero high.q1 := inferInstanceAs (NeZero q)
  let _ : NeZero high.d := inferInstanceAs (NeZero d)
  let _ : NeZero high.q := inferInstanceAs (NeZero 1)
  have gF := Chr.levGal F low.N low.H (hostLevel low F lf)
  have gE := Chr.levGal E high.N high.H (hostLevel high E uf)
  have f := (gF.2.2 Ω).1
  have u := (gE.2.2 Ω).1
  have le : galOf ℚ E Ω ≤ galOf ℚ F Ω := by
    intro g hg
    rw [u, field_conditions] at hg
    rw [f, field_conditions]
    refine ⟨⟨⟨?_, hg.1.1.2⟩, hg.1.2⟩, hg.2⟩
    have hdv : 2 ^ (i + 2) ∣ 2 ^ (j + 2) := pow_dvd_pow _ (by omega)
    rw [← reduce_cls hdv g]
    exact neg_one_restrict _ _ hg.1.1.1
  refine ⟨gE.1, le, ?_, ?_⟩
  · intro g hg
    have hf : g ∈ galOf ℚ F Ω := hg.1
    have hcy : cycZ ℚ Ω 2 g = 1 := hg.2
    rw [f, field_conditions] at hf
    rw [u, field_conditions]
    refine ⟨⟨⟨?_, hf.1.1.2⟩, hf.1.2⟩, hf.2⟩
    rw [cls_at_two (show cycZ ℚ Ω 2 g = 1 from hcy)]
    exact Subgroup.one_mem _
  · have hdv : (galOf ℚ E Ω).relIndex (galOf ℚ F Ω) ∣ (galOf ℚ E Ω).index :=
      dvd_of_mul_right_eq _ (Subgroup.relIndex_mul_index le)
    have hcard : (galOf ℚ E Ω).index = high.H.index := u ▸ (gE.2.2 Ω).2.1
    have h : (galOf ℚ E Ω).relIndex (galOf ℚ F Ω) ∣ 2 ^ (j + 2) := by
      apply hdv.trans
      rw [hcard]
      have ho : high.o = 1 := orderOf_one
      simpa only [ho, mul_one] using (hostIndex high).1
    obtain ⟨v, _, hv⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
    exact ⟨v, hv⟩

end RiemannReduction.ConductorOne
