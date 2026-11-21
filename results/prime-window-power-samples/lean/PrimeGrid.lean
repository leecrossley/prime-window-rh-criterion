import Mathlib

namespace RiemannReduction.PrimeGrid
open Finset

abbrev primes := Nat.primesLE

private lemma mem_primes {j p : ℕ} : p ∈ primes j ↔ p ≤ j ∧ p.Prime := Nat.mem_primesLE

/-- The common denominator of all prime terms at grid position j. -/
abbrev denominator := primorial

def height (j p : ℕ) : ℕ :=
  if j ≤ p then 0 else if j ≤ 2*p then 2*(j-p) else 4*p-j

def primeProduct (j : ℕ) : ℕ :=
  ∏ p ∈ primes j, p ^ ((denominator j / p) * height j p)

/-- A comparison of positive integers, with no zeta function or logarithms. -/
def Passes (j : ℕ) : Prop := primeProduct j ≤ 2 ^ (j * denominator j)

private def hinge (u : ℝ) (k : ℕ) := max (u-k) 0

/-- The band weight at upper endpoint u = 4y. -/
noncomputable def weight (u : ℝ) (p : ℕ) : ℝ :=
  (2 * hinge u p - 3 * hinge u (2*p) + hinge u (4*p)) / (2*p)

noncomputable def sumTo (N : ℕ) (u : ℝ) : ℝ := ∑ p ∈ primes N, Real.log p * weight u p

private lemma hinge_integer (j k : ℕ) : hinge j k = ((j-k : ℕ) : ℝ) := by
  by_cases hk : k ≤ j
  · simp [hinge, Nat.cast_sub hk, max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr hk))]
  · simp [hinge, Nat.sub_eq_zero_of_le (le_of_not_ge hk),
      max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr (le_of_not_ge hk)))]

lemma weight_integer (j p : ℕ) : weight j p = (height j p : ℝ) / (2*p) := by
  have id : height j p + 3*(j-2*p) = 2*(j-p) + (j-4*p) := by
    unfold height
    split_ifs <;> omega
  have h := congrArg ((↑) : ℕ → ℝ) id
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
  simp only [weight, hinge_integer]
  congr 1
  linarith

private lemma log_primeProduct (j : ℕ) :
    Real.log (primeProduct j) = (2 * denominator j : ℝ) * sumTo j j := by
  unfold primeProduct sumTo
  push_cast
  rw [Real.log_prod (fun p hp => pow_ne_zero _ (Nat.cast_ne_zero.mpr (mem_primes.mp hp).2.ne_zero)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpos : 0 < (p : ℝ) := Nat.cast_pos.mpr (mem_primes.mp hp).2.pos
  have hd : p ∣ denominator j := Finset.dvd_prod_of_mem (fun k : ℕ => k) hp
  have cancel : (↑(denominator j / p) : ℝ) * p = denominator j := by
    exact_mod_cast Nat.div_mul_cancel hd
  rw [Real.log_pow, weight_integer]
  push_cast
  field_simp [hpos.ne']
  linear_combination ((height j p : ℝ) * Real.log p) * cancel

theorem passes_iff (j : ℕ) :
    Passes j ↔ sumTo j j ≤ (j : ℝ) / 2 * Real.log 2 := by
  have hD : 0 < denominator j := Finset.prod_pos fun p hp => (mem_primes.mp hp).2.pos
  have hP : 0 < primeProduct j :=
    Finset.prod_pos fun p hp => pow_pos (mem_primes.mp hp).2.pos _
  have hD' : 0 < (denominator j : ℝ) := Nat.cast_pos.mpr hD
  have hlog := Real.log_le_log_iff (Nat.cast_pos.mpr hP)
    (show 0 < (↑(2^(j * denominator j) : ℕ) : ℝ) by positivity)
  unfold Passes
  rw [← Nat.cast_le (α := ℝ), ← hlog, log_primeProduct]
  push_cast
  rw [Real.log_pow]
  push_cast
  rw [show (j : ℝ) * denominator j * Real.log 2 =
    (2 * denominator j : ℝ) * ((j : ℝ)/2 * Real.log 2) by ring]
  exact mul_le_mul_iff_right₀ (by positivity)

private lemma hinge_interpolate (j k : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    hinge ((j : ℝ)+t) k = (1-t)*hinge j k + t*hinge (j+1 : ℕ) k := by
  have jc : ((j+1 : ℕ) : ℝ) = (j : ℝ)+1 := by push_cast; rfl
  by_cases h : k ≤ j
  · have hk : (k : ℝ) ≤ j := Nat.cast_le.mpr h
    simp only [hinge, jc]
    rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  · have hk : (j : ℝ)+1 ≤ k := by exact_mod_cast (show j+1 ≤ k by omega)
    simp only [hinge, jc]
    rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
    ring

lemma sumTo_interpolate (N j : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    sumTo N ((j : ℝ)+t) = (1-t)*sumTo N j + t*sumTo N (j+1 : ℕ) := by
  simp only [sumTo, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [weight, hinge_interpolate j _ ht ht1]
  ring

lemma weight_zero_before {u : ℝ} {p : ℕ} (h : u ≤ p) : weight u p = 0 := by
  have h2 : u ≤ (↑(2*p : ℕ) : ℝ) := h.trans (by exact_mod_cast (show p ≤ 2*p by omega))
  have h4 : u ≤ (↑(4*p : ℕ) : ℝ) := h.trans (by exact_mod_cast (show p ≤ 4*p by omega))
  simp only [weight, hinge, max_eq_right (sub_nonpos.mpr h), max_eq_right (sub_nonpos.mpr h2),
    max_eq_right (sub_nonpos.mpr h4), mul_zero, sub_zero, add_zero, zero_div]

/-- Increasing the prime cutoff beyond the upper endpoint adds zero terms. -/
lemma sumTo_extend {j N : ℕ} (hj : j ≤ N) {u : ℝ} (hu : u < (j : ℝ)+1) :
    sumTo j u = sumTo N u := by
  apply Finset.sum_subset (fun p hp => mem_primes.mpr ⟨(mem_primes.mp hp).1.trans hj, (mem_primes.mp hp).2⟩)
  intro p hp h
  have hjp : j < p := by
    by_contra! hle
    exact h (mem_primes.mpr ⟨hle,(mem_primes.mp hp).2⟩)
  have hc : (j : ℝ)+1 ≤ p := by exact_mod_cast (Nat.succ_le_of_lt hjp)
  simp [weight_zero_before (hu.trans_le hc).le]

noncomputable def margin (u : ℝ) := u/2 * Real.log 2 - sumTo ⌊u⌋₊ u

private lemma margin_nat (j : ℕ) :
    margin j = (j:ℝ)/2 * Real.log 2 - sumTo j j := by simp [margin]

lemma passes_iff_margin (j : ℕ) : Passes j ↔ 0 ≤ margin j := by
  rw [margin_nat, sub_nonneg, passes_iff]

private theorem margin_interpolation {a b : ℕ} {u : ℝ} (ha : (a:ℝ) ≤ u) (hb : u ≤ (b:ℝ)) :
    ∃ j ∈ Finset.Icc a b, ∃ k ∈ Finset.Icc a b, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      margin u = (1-t)*margin j + t*margin k := by
  have hu : 0 ≤ u := (Nat.cast_nonneg _).trans ha
  let j := ⌊u⌋₊
  have lo : (j : ℝ) ≤ u := Nat.floor_le hu
  have hi : u < (j : ℝ)+1 := Nat.lt_floor_add_one u
  have aj : a ≤ j := (Nat.le_floor_iff hu).mpr ha
  have jb : j ≤ b := by exact_mod_cast lo.trans hb
  have hj : j ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨aj,jb⟩
  by_cases h : u = (j : ℝ)
  · exact ⟨j, hj, j, hj, 0, le_rfl, zero_le_one, by simp [h]⟩
  have j1 : j+1 ≤ b := by
    by_contra! hn
    have e : j = b := by omega
    exact h (le_antisymm (by simpa only [e] using hb) lo)
  let t := u-j
  have t0 : 0 ≤ t := sub_nonneg.mpr lo
  have t1 : t ≤ 1 := by dsimp [t]; linarith
  have eq : (j : ℝ)+t = u := by dsimp [t]; ring
  refine ⟨j, hj, j+1, Finset.mem_Icc.mpr ⟨by omega,j1⟩, t, t0, t1, ?_⟩
  rw [margin_nat j, margin_nat (j+1)]
  change u/2 * Real.log 2 - sumTo j u = _
  have linear : sumTo j u = (1-t)*sumTo j j + t*sumTo (j+1) (j+1 : ℕ) := by
    rw [sumTo_extend (N := j+1) (by omega) hi, ← eq, sumTo_interpolate _ _ t0 t1,
      sumTo_extend (N := j+1) (by omega) (by linarith : (j:ℝ) < (j:ℝ)+1)]
  rw [linear]
  push_cast
  dsimp [t]
  ring

/-- All integer checks in a closed block control every real point in that block. -/
theorem block_bound {a b : ℕ} (checks : ∀ j ∈ Finset.Icc a b, Passes j)
    {u : ℝ} (ha : (a : ℝ) ≤ u) (hb : u ≤ (b : ℝ)) :
    sumTo ⌊u⌋₊ u ≤ u/2 * Real.log 2 := by
  obtain ⟨j,hj,k,hk,t,t0,t1,eq⟩ := margin_interpolation ha hb
  have h i hi := (passes_iff_margin i).mp (checks i hi)
  apply sub_nonneg.mp (show 0 ≤ margin u from ?_)
  rw [eq]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr t1) (h j hj)) (mul_nonneg t0 (h k hk))

/-- A strict positive margin anywhere in the block forces at least one integer to pass. -/
theorem exists_pass_of_strict_bound {a b : ℕ} {u : ℝ} (ha : (a : ℝ) ≤ u) (hb : u ≤ (b : ℝ))
    (below : sumTo ⌊u⌋₊ u < u/2 * Real.log 2) : ∃ j ∈ Finset.Icc a b, Passes j := by
  obtain ⟨j,hj,k,hk,t,t0,t1,eq⟩ := margin_interpolation ha hb
  by_contra! fail
  have h i hi := (lt_of_not_ge fun hh => fail i hi ((passes_iff_margin i).mpr hh)).le
  have pos : 0 < margin u := sub_pos.mpr below
  rw [eq] at pos
  exact pos.not_ge (add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr t1) (h j hj))
    (mul_nonpos_of_nonneg_of_nonpos t0 (h k hk)))

#print axioms passes_iff
#print axioms block_bound
end RiemannReduction.PrimeGrid
