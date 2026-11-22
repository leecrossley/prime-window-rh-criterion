import RealUnitResidueSigns
import RealCyclotomicUnit
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-! The three units of the full dyadic cyclotomic field at its actual prime ideals. -/
noncomputable section
open NumberField
namespace RiemannReduction.UnitSigns
open UnitResidue CyclotomicUnits

def squareAt {R : Type*} [CommRing R] (P : Ideal R) (x : R) : Prop :=
  IsSquare (Ideal.Quotient.mk P x)

private theorem reduced_real {R F : Type*} [CommRing R] [Field F] (f : R →+* F) (z : Rˣ) :
    f (realUnitFactor z) = realUnit (f z) := by
  simp only [realUnitFactor, realUnit, map_add, map_one]
  congr 1
  exact Units.val_inv_eq_inv_val (Units.map f.toMonoidHom z)

theorem integral_units {R : Type*} [CommRing R] [IsDomain R] {j : ℕ} (z : Rˣ)
    (hz : IsPrimitiveRoot (z : R) (2^(j+4))) :
    IsUnit (realUnitFactor z) ∧ IsUnit (realUnitFactor (z^3)) :=
  ⟨real_cyclotomic_factor_isUnit z (j+1) hz,
   real_cyclotomic_factor_isUnit (z^3) (j+1)
     (hz.pow_of_coprime 3 ((by decide : Nat.Coprime 3 2).pow_right _))⟩

variable {j p : ℕ} {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {2^(j+4)} ℚ K]

omit [IsCyclotomicExtension {2^(j+4)} ℚ K] in
private theorem residue_data (hp : p.Prime) (gt : 2 < p) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] {z : (𝓞 K)ˣ} (root : IsPrimitiveRoot (z : 𝓞 K) (2^(j+4))) :
    IsPrimitiveRoot (Ideal.Quotient.mk P (z : 𝓞 K)) (2^(j+4)) ∧ CharP (𝓞 K ⧸ P) p := by
  let : Fact p.Prime := ⟨hp⟩
  have nd : ¬ p ∣ 2^(j+4) := fun h => by
    have := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow h); omega
  have cop : (Ideal.absNorm P).Coprime (2^(j+4)) := by
    rw [← Ideal.pow_inertiaDeg p]
    exact (hp.coprime_iff_not_dvd.mpr nd).pow_left _
  refine ⟨root.idealQuotient_mk (by simpa using (inferInstance : P.IsPrime).ne_top) cop,
    (CharP.charP_iff_prime_eq_zero hp).mpr ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
  simpa only [map_natCast, Int.cast_natCast, Int.cast_ofNat] using
    (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).mp (Ideal.subset_span (by simp))

/-- Above q both real units are nonsquares. Above d exactly one is a nonsquare. -/
theorem signs_at_primes {q d : ℕ} (hq : q.Prime) (q8 : q % 8 = 3) (hd : d.Prime)
    (d16 : d % 16 = 7) (P Q : Ideal (𝓞 K)) [P.IsPrime] [Q.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] [Q.LiesOver (Ideal.span {(d : ℤ)})]
    (z : (𝓞 K)ˣ) (root : IsPrimitiveRoot (z : 𝓞 K) (2^(j+4))) :
    (¬ squareAt P (realUnitFactor z) ∧ ¬ squareAt P (realUnitFactor (z^3))) ∧
    (squareAt Q (realUnitFactor z) ↔ ¬ squareAt Q (realUnitFactor (z^3))) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  let : Fact d.Prime := ⟨hd⟩
  have pn := Ideal.ne_bot_of_liesOver_of_ne_bot (show Ideal.span {(q : ℤ)} ≠ ⊥ by simp [hq.ne_zero]) P
  have qn := Ideal.ne_bot_of_liesOver_of_ne_bot (show Ideal.span {(d : ℤ)} ≠ ⊥ by simp [hd.ne_zero]) Q
  let : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal pn
  let : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal qn
  let : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let : Field (𝓞 K ⧸ Q) := Ideal.Quotient.field Q
  let : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient pn
  let : Finite (𝓞 K ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient qn
  let := Fintype.ofFinite (𝓞 K ⧸ P)
  let := Fintype.ofFinite (𝓞 K ⧸ Q)
  obtain ⟨rp, cp⟩ := residue_data hq (by omega) P root
  obtain ⟨rd, cd⟩ := residue_data hd (by omega) Q root
  have ⟨nsq,nsd⟩ := zeta_nonsquare hq q8 hd d16 K P Q root
  have qsign := at_q q8 rp (quadraticChar_neg_one_iff_not_isSquare.mpr nsq)
  have qsign3 := at_q q8 (rp.pow_of_coprime 3 ((by decide : Nat.Coprime 3 2).pow_right _))
    (by rw [map_pow,quadraticChar_neg_one_iff_not_isSquare.mpr nsq]; decide)
  have half : (Ideal.Quotient.mk Q (z : 𝓞 K))^(2^(j+3)) = -1 := by
    apply IsPrimitiveRoot.eq_neg_one_of_two_right
    apply rd.pow (by positivity)
    rw [pow_succ 2 (j+3),mul_comm]
  have minus : quadraticChar (𝓞 K ⧸ Q) (-1) = 1 := by
    rw [← half,pow_succ 2 (j+2),pow_mul]
    exact quadraticChar_sq_one' (pow_ne_zero _ (rd.ne_zero (by positivity)))
  have dsign := at_d d16 rd (quadraticChar_neg_one_iff_not_isSquare.mpr nsd) minus
  have qunit := integral_units z root
  have nz (x : 𝓞 K) (hx : IsUnit x) : Ideal.Quotient.mk Q x ≠ 0 := (hx.map (Ideal.Quotient.mk Q)).ne_zero
  have r1 := quadraticChar_dichotomy (nz _ qunit.1)
  have r3 := quadraticChar_dichotomy (nz _ qunit.2)
  simp only [reduced_real, Units.val_pow_eq_pow_val,map_pow] at r1 r3
  unfold squareAt
  simp only [reduced_real,Units.val_pow_eq_pow_val,map_pow]
  refine ⟨⟨quadraticChar_neg_one_iff_not_isSquare.mp qsign,
    quadraticChar_neg_one_iff_not_isSquare.mp qsign3⟩, ?_⟩
  have nz1 := nz _ qunit.1
  rw [reduced_real] at nz1
  rw [← quadraticChar_one_iff_isSquare nz1,← quadraticChar_neg_one_iff_not_isSquare]
  rcases r1 with e | e <;> rcases r3 with f | f <;> simp only [e,f] at dsign ⊢ <;> omega

end RiemannReduction.UnitSigns
