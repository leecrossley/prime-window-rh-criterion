import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The nonsquare root-of-unity row in the dyadic cyclotomic layers.
The cardinalities are the residue field sizes at the indicated residue degrees. -/

namespace RiemannReduction.UnitResidue

/-- The exact power of two dividing the predecessor of a finite field size. -/
def ExactTwoPart (e N : ℕ) : Prop := ∃ k : ℕ, N = 1 + 2 ^ e * (2 * k + 1)

private theorem square_step {n x : ℕ} (h : ExactTwoPart (n + 2) x) :
    ExactTwoPart (n + 3) (x ^ 2) := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k + 2^n * (2*k + 1)^2, ?_⟩
  simp only [pow_add]
  ring

private theorem iterate {n x : ℕ} (h : ExactTwoPart (n + 2) x) (j : ℕ) :
    ExactTwoPart (n + 2 + j) (x ^ (2^j)) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [pow_succ 2 j, pow_mul]
    have prev : ExactTwoPart (n+j+2) (x^(2^j)) := by
      rwa [show n+j+2 = n+2+j by omega]
    convert square_step prev using 1
    omega

private theorem q_start {q : ℕ} (h : q % 8 = 3) : ExactTwoPart 3 (q^2) := by
  let k := q / 8
  have hk : q = 8*k+3 := by dsimp [k]; omega
  refine ⟨4*k^2+3*k, ?_⟩
  calc
    q^2 = (8*k+3)^2 := congrArg (·^2) hk
    _ = _ := by ring

private theorem d_start {d : ℕ} (h : d % 16 = 7) : ExactTwoPart 4 (d^2) := by
  let k := d / 16
  have hk : d = 16*k+7 := by dsimp [k]; omega
  refine ⟨8*k^2+7*k+1, ?_⟩
  calc
    d^2 = (16*k+7)^2 := congrArg (·^2) hk
    _ = _ := by ring

/-- At a common conductor 2^(j+4), the two residue degrees are
2^(j+2) over q and 2^(j+1) over d. Both sizes minus one have exact
2-part 2^(j+4). -/
theorem two_parts {q d : ℕ} (hq : q % 8 = 3) (hd : d % 16 = 7) (j : ℕ) :
    ExactTwoPart (j+4) (q^(2^(j+2))) ∧ ExactTwoPart (j+4) (d^(2^(j+1))) := by
  have h1 := iterate (n := 1) (q_start hq) (j+1)
  have h2 := iterate (n := 2) (d_start hd) j
  constructor
  · convert h1 using 1
    · omega
    · rw [← pow_mul, show j+2 = (j+1)+1 by omega, pow_succ 2 (j+1), mul_comm]
  · convert h2 using 1
    · omega
    · rw [← pow_mul, pow_succ 2 j, mul_comm]

private theorem congruences {n x : ℕ} (h : ExactTwoPart n x) :
    Nat.ModEq (2^n) 1 x ∧ ¬ Nat.ModEq (2^(n+1)) 1 x := by
  obtain ⟨k,rfl⟩ := h
  have le : 1 ≤ 1 + 2^n * (2*k+1) := by omega
  rw [Nat.modEq_iff_dvd' le, Nat.modEq_iff_dvd' le, Nat.add_sub_cancel_left, pow_succ]
  refine ⟨dvd_mul_right _ _, fun h => ?_⟩
  have : 2 ∣ 2*k+1 := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2^n)).mp h
  omega

private theorem pow_congr {p e N : ℕ} :
    (p : ZMod N)^e = 1 ↔ Nat.ModEq N 1 (p^e) := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one, Nat.cast_pow, eq_comm]

/-- The multiplicative orders of the two congruence classes at every
conductor 2^(j+4). -/
theorem orders {q d : ℕ} (hq : q % 8 = 3) (hd : d % 16 = 7) (j : ℕ) :
    orderOf (q : ZMod (2^(j+4))) = 2^(j+2) ∧
    orderOf (d : ZMod (2^(j+4))) = 2^(j+1) := by
  obtain ⟨qf,df⟩ := two_parts hq hd j
  constructor
  · apply orderOf_eq_prime_pow (n := j+1) _ (pow_congr.mpr (congruences qf).1)
    have hs := iterate (n := 1) (q_start hq) j
    have hh : ExactTwoPart (j+3) (q^(2^(j+1))) := by
      convert hs using 1
      · omega
      · rw [← pow_mul, pow_succ 2 j, mul_comm]
    exact fun e => (congruences hh).2 (pow_congr.mp e)
  · apply orderOf_eq_prime_pow (n := j) _ (pow_congr.mpr (congruences df).1)
    intro e
    have hc := pow_congr.mp e
    cases j with
    | zero =>
      change 1 % 16 = (d ^ (2^0)) % 16 at hc
      simp only [pow_zero, pow_one, Nat.mod_eq_of_lt (by decide : 1 < 16)] at hc
      omega
    | succ j =>
      exact (congruences (two_parts hq hd j).2).2 hc

/-- In a finite field with this exact dyadic order, every root of unity
of the full 2-power order is a nonsquare. -/
theorem not_square {F : Type*} [Field F] [Fintype F] {n : ℕ} {z : F}
    (hs : ExactTwoPart (n+1) (Fintype.card F)) (hz : IsPrimitiveRoot z (2^(n+1))) :
    ¬ IsSquare z := by
  obtain ⟨k, card⟩ := hs
  rintro ⟨y, hy⟩
  have nz : y ≠ 0 := by
    intro h
    exact hz.ne_zero (by positivity) (by simp [hy,h])
  have exp : Fintype.card F - 1 = 2 * (2^n * (2*k+1)) := by
    rw [card, Nat.add_sub_cancel_left, pow_succ]; ring
  have h := FiniteField.pow_card_sub_one_eq_one y nz
  rw [exp, pow_mul, sq, ← hy] at h
  have div := hz.dvd_of_pow_eq_one _ h
  rw [pow_succ] at div
  have : 2 ∣ 2*k+1 := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2^n)).mp div
  omega

open NumberField in
private theorem nonsquare_at_prime {n p e : ℕ} (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {2^(n+1)} ℚ K] (hp : p.Prime) (nd : ¬ p ∣ 2^(n+1))
    (order : orderOf (p : ZMod (2^(n+1))) = e) (hs : ExactTwoPart (n+1) (p^e))
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    {z : 𝓞 K} (root : IsPrimitiveRoot z (2^(n+1))) :
    ¬ IsSquare (Ideal.Quotient.mk P z) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have base : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [hp.ne_zero]
  have nz := Ideal.ne_bot_of_liesOver_of_ne_bot base P
  let : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal nz
  let : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient nz
  let := Fintype.ofFinite (𝓞 K ⧸ P)
  have degree := IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 2^(n+1)) p K P nd
  have card : Fintype.card (𝓞 K ⧸ P) = p^e := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      ← Ideal.pow_inertiaDeg p, degree, order]
  have cop : (Ideal.absNorm P).Coprime (2^(n+1)) := by
    rw [← Ideal.pow_inertiaDeg p, degree, order]
    exact (hp.coprime_iff_not_dvd.mpr nd).pow_left e
  apply not_square (card ▸ hs)
  exact root.idealQuotient_mk (by simpa using (inferInstance : P.IsPrime).ne_top) cop

private theorem odd_prime {p j : ℕ} (hp : p.Prime) (gt : 2 < p) : ¬ p ∣ 2^(j+4) := by
  intro h
  have := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow h)
  omega

open NumberField in
private theorem count_times_order {p j : ℕ} (hp : p.Prime) (gt : 2 < p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {2^(j+4)} ℚ K] :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard * orderOf (p : ZMod (2^(j+4))) =
      2^(j+3) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {2^(j+4)} ℚ K
  have nd := odd_prime (j := j) hp gt
  have count := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K nd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K nd, one_mul,
    IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K, IsCyclotomicExtension.Rat.finrank (2^(j+4)) K,
    Nat.totient_prime_pow_succ Nat.prime_two (j+3), show 2-1=1 by decide, mul_one] at count
  exact count

open NumberField in
/-- At every conductor 2^(j+4), exactly two primes lie above q and four
above d in the full cyclotomic field. -/
theorem prime_counts {q d j : ℕ} (hq : q.Prime) (q8 : q % 8 = 3)
    (hd : d.Prime) (d16 : d % 16 = 7) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {2^(j+4)} ℚ K] :
    ((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)).ncard = 2 ∧
    ((Ideal.span {(d : ℤ)}).primesOver (𝓞 K)).ncard = 4 := by
  obtain ⟨qo, dO⟩ := orders q8 d16 j
  have qcount := count_times_order (j := j) hq (by omega) K
  have dcount := count_times_order (j := j) hd (by omega) K
  rw [qo] at qcount
  rw [dO] at dcount
  constructor
  · apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2^(j+2))
    rw [qcount, pow_succ 2 (j+2), mul_comm]
  · apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2^(j+1))
    rw [dcount]; simp only [pow_add]; ring

open NumberField in
/-- At every prime above q or d in the full dyadic cyclotomic field of
conductor 2^(j+4), a primitive integral root of that order is a nonsquare
in the residue field. Both residue degrees are proved from the congruences. -/
theorem zeta_nonsquare {q d j : ℕ} (hq : q.Prime) (q8 : q % 8 = 3)
    (hd : d.Prime) (d16 : d % 16 = 7) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {2^(j+4)} ℚ K]
    (P Q : Ideal (𝓞 K)) [P.IsPrime] [Q.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] [Q.LiesOver (Ideal.span {(d : ℤ)})]
    {z : 𝓞 K} (root : IsPrimitiveRoot z (2^(j+4))) :
    ¬ IsSquare (Ideal.Quotient.mk P z) ∧ ¬ IsSquare (Ideal.Quotient.mk Q z) := by
  obtain ⟨qo, dO⟩ := orders q8 d16 j
  obtain ⟨qp, dp⟩ := two_parts q8 d16 j
  exact ⟨nonsquare_at_prime (n := j+3) K hq (odd_prime hq (by omega)) qo qp P root,
    nonsquare_at_prime (n := j+3) K hd (odd_prime hd (by omega)) dO dp Q root⟩

open NumberField in
/-- The canonical cyclotomic unit has the all-nonsquare row, for every
choice of a prime above either auxiliary prime. -/
theorem root_of_unity_row {q d j : ℕ} (hq : q.Prime) (q8 : q % 8 = 3)
    (hd : d.Prime) (d16 : d % 16 = 7) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {2^(j+4)} ℚ K]
    (P Q : Ideal (𝓞 K)) [P.IsPrime] [Q.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] [Q.LiesOver (Ideal.span {(d : ℤ)})] :
    (((Ideal.span {(q : ℤ)}).primesOver (𝓞 K)).ncard = 2 ∧
      ((Ideal.span {(d : ℤ)}).primesOver (𝓞 K)).ncard = 4) ∧
    (let z := (IsCyclotomicExtension.zeta_spec (2^(j+4)) ℚ K).toInteger
     ¬ IsSquare (Ideal.Quotient.mk P z) ∧ ¬ IsSquare (Ideal.Quotient.mk Q z)) :=
  ⟨prime_counts (j := j) hq q8 hd d16 K, zeta_nonsquare (j := j) hq q8 hd d16 K P Q
    (IsCyclotomicExtension.zeta_spec (2^(j+4)) ℚ K).toInteger_isPrimitiveRoot⟩

#print axioms prime_counts
#print axioms root_of_unity_row

end RiemannReduction.UnitResidue
