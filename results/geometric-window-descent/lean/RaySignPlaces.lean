import RealUnitSignRows
import ReciprocityTheory.GaloisValuations.ArithOfA

/-! Six finite places labelled by the square classes of three global units. -/
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Gal
namespace RiemannReduction.UnitSigns
open UnitResidue CyclotomicUnits
abbrev Sites := Fin 3 × Bool

structure SignPlaces (K : Type) [Field K] [NumberField K] (q d : ℕ) where
  v : Sites → HeightOneSpectrum (𝓞 K)
  inj : Function.Injective v
  covers : ∀ W, (↑(q*d) : 𝓞 K) ∈ W.asIdeal ↔ W ∈ Set.range v
  odd : ∀ t, (2 : 𝓞 K) ∉ (v t).asIdeal
  z : (𝓞 K)ˣ
  u : (𝓞 K)ˣ
  c : (𝓞 K)ˣ
  root : ∀ t, ¬ squareAt (v t).asIdeal (z : 𝓞 K)
  first : ∀ t, squareAt (v t).asIdeal (u : 𝓞 K) ↔ t.1 = 2
  second : ∀ t, squareAt (v t).asIdeal (c : 𝓞 K) ↔ t.1 = 1

private def height {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (P : Above K p) :
    HeightOneSpectrum (𝓞 K) :=
  ⟨P.1,P.2.1,Ideal.ne_bot_of_mem_primesOver (show Ideal.span {(p:ℤ)} ≠ ⊥ by simp [hp.ne_zero]) P.2⟩

private def pairOfTwo {T : Type*} (h : Nat.card T = 2) : Bool ≃ T := by
  have : Finite T := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card T)).2
  let := Fintype.ofFinite T
  apply Fintype.equivOfCardEq
  rwa [Fintype.card_bool,← Nat.card_eq_fintype_card,eq_comm]

theorem sign_places {K : Type} [Field K] [NumberField K] {q d j : ℕ}
    [IsCyclotomicExtension {2^(j+4)} ℚ K]
    (hq : q.Prime) (q8 : q%8=3) (hd : d.Prime) (d16 : d%16=7) :
    Nonempty (SignPlaces K q d) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  let : Fact d.Prime := ⟨hd⟩
  let root := (IsCyclotomicExtension.zeta_spec (2^(j+4)) ℚ K).toInteger_isPrimitiveRoot
  let z := (root.isUnit (by positivity)).unit
  have hz : IsPrimitiveRoot (z : 𝓞 K) (2^(j+4)) := by simpa only [z, IsUnit.unit_spec] using root
  obtain ⟨qc,pc,nc⟩ := row_counts hq q8 hd d16 z hz
  let a := pairOfTwo qc
  let b := pairOfTwo nc
  let c := pairOfTwo pc
  let v : Sites → HeightOneSpectrum (𝓞 K) := fun t => ![height hq (a t.2),
    height hd (b t.2).1, height hd (c t.2).1] t.1
  let unitA := (integral_units z hz).1
  let unitB := (integral_units z hz).2
  have qmem (Q : Above K q) : (q : 𝓞 K) ∈ Q.1 := (liesOver_span_iff q Q.1).mp Q.2.2
  have dmem (Q : Above K d) : (d : 𝓞 K) ∈ Q.1 := (liesOver_span_iff d Q.1).mp Q.2.2
  have only (p k : ℕ) (Q : Above K p) (h : (k : 𝓞 K) ∈ Q.1) : p ∣ k := by
    have h' := (Ideal.mem_of_liesOver Q.1 (Ideal.span {(p:ℤ)}) (k:ℤ)).mpr (by simpa using h)
    rw [Ideal.mem_span_singleton] at h'
    exact_mod_cast h'
  have qrow (t : Sites) : (q : 𝓞 K) ∈ (v t).asIdeal ↔ t.1 = 0 := by
    obtain ⟨i,k⟩ := t
    fin_cases i
    · exact iff_of_true (qmem _) rfl
    · exact iff_of_false (fun h => by have := hq.eq_one_or_self_of_dvd d (only d q (b k).1 h); omega) (by decide +revert)
    · exact iff_of_false (fun h => by have := hq.eq_one_or_self_of_dvd d (only d q (c k).1 h); omega) (by decide +revert)
  have first (t : Sites) : squareAt (v t).asIdeal (realUnitFactor z) ↔ t.1 = 2 := by
    obtain ⟨i,k⟩ := t
    fin_cases i
    · exact iff_of_false (signs_at_primes hq q8 hd d16 (a k).1 (b k).1.1 z hz).1.1 (by decide +revert)
    · exact iff_of_false (b k).2 (by decide +revert)
    · exact iff_of_true (c k).2 rfl
  have second (t : Sites) : squareAt (v t).asIdeal (realUnitFactor (z^3)) ↔ t.1 = 1 := by
    obtain ⟨i,k⟩ := t
    fin_cases i
    · exact iff_of_false (signs_at_primes hq q8 hd d16 (a k).1 (b k).1.1 z hz).1.2 (by decide +revert)
    · have e := (signs_at_primes hq q8 hd d16 (a k).1 (b k).1.1 z hz).2
      exact iff_of_true (by by_contra hn; exact (b k).2 (e.mpr hn)) rfl
    · exact iff_of_false ((signs_at_primes hq q8 hd d16 (a k).1 (c k).1.1 z hz).2.mp (c k).2) (by decide +revert)
  refine ⟨⟨v,?_,?_,?_,z,unitA.unit,unitB.unit,?_,by simpa only [IsUnit.unit_spec] using first,
    by simpa only [IsUnit.unit_spec] using second⟩⟩
  · rintro ⟨i,k⟩ ⟨l,m⟩ eq
    have h0 := (qrow (i,k)).symm.trans (eq ▸ qrow (l,m))
    have h2 := (first (i,k)).symm.trans (eq ▸ first (l,m))
    have eil : i = l := by change (i=0 ↔ l=0) at h0; change (i=2 ↔ l=2) at h2; omega
    subst l
    apply congrArg (Prod.mk i)
    have e := congrArg HeightOneSpectrum.asIdeal eq
    fin_cases i
    · exact a.injective (Subtype.ext e)
    · exact b.injective (Subtype.ext (Subtype.ext e))
    · exact c.injective (Subtype.ext (Subtype.ext e))
  · intro W
    rw [Nat.cast_mul, W.isPrime.mul_mem_iff_mem_or_mem]
    constructor
    · rintro (h|h)
      · let Q : Above K q := ⟨W.asIdeal,W.isPrime,(liesOver_span_iff q W.asIdeal).mpr h⟩
        exact ⟨(0,a.symm Q),by change height hq (a (a.symm Q)) = W; rw [a.apply_symm_apply]; rfl⟩
      · let Q : Above K d := ⟨W.asIdeal,W.isPrime,(liesOver_span_iff d W.asIdeal).mpr h⟩
        by_cases sq : squareAt Q.1 (realUnitFactor z)
        · let T := (⟨Q,sq⟩ : {Q : Above K d // squareAt Q.1 (realUnitFactor z)})
          exact ⟨(2,c.symm T),by change height hd (c (c.symm T)).1 = W; rw [c.apply_symm_apply]; rfl⟩
        · let T := (⟨Q,sq⟩ : {Q : Above K d // ¬ squareAt Q.1 (realUnitFactor z)})
          exact ⟨(1,b.symm T),by change height hd (b (b.symm T)).1 = W; rw [b.apply_symm_apply]; rfl⟩
    · rintro ⟨⟨i,k⟩,rfl⟩
      fin_cases i
      · exact Or.inl (qmem _)
      · exact Or.inr (dmem _)
      · exact Or.inr (dmem _)
  · rintro ⟨i,k⟩ h
    fin_cases i
    · have := Nat.le_of_dvd (by decide : 0 < 2) (only q 2 (a k) h); omega
    · have := Nat.le_of_dvd (by decide : 0 < 2) (only d 2 (b k).1 h); omega
    · have := Nat.le_of_dvd (by decide : 0 < 2) (only d 2 (c k).1 h); omega
  · rintro ⟨i,k⟩
    fin_cases i
    · exact (zeta_nonsquare hq q8 hd d16 K (a k).1 (b k).1.1 hz).1
    · exact (zeta_nonsquare hq q8 hd d16 K (a k).1 (b k).1.1 hz).2
    · exact (zeta_nonsquare hq q8 hd d16 K (a k).1 (c k).1.1 hz).2

end RiemannReduction.UnitSigns
