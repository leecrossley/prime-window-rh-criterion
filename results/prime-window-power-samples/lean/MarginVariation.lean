import PrimeGrid

open Finset
namespace RiemannReduction.PrimeGrid

private lemma weight_zero_after {u : ℝ} {p : ℕ} (h : 4*(p:ℝ) ≤ u) : weight u p = 0 := by
  change (2*max (u-p) 0 - 3*max (u-↑(2*p : ℕ)) 0 + max (u-↑(4*p : ℕ)) 0)/(2*p) = 0
  push_cast
  have hp := Nat.cast_nonneg (α := ℝ) p
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

private lemma weight_rise {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) {p : ℕ} (hp : 0 < p) :
    weight v p - weight u p ≤ 6*(v-u)/u := by
  by_cases past : 4*(p:ℝ) ≤ u
  · rw [weight_zero_after (past.trans huv), weight_zero_after past]
    rw [sub_self]
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr huv)) hu.le
  have pp : 0 < (p:ℝ) := Nat.cast_pos.mpr hp
  have bump (k : ℝ) : max (v-k) 0 - max (u-k) 0 ≤ v-u := by
    have ab := abs_max_sub_max_le_abs (v-k) (u-k) 0
    calc _ ≤ |max (v-k) 0 - max (u-k) 0| := le_abs_self _
         _ ≤ |(v-k)-(u-k)| := ab
         _ = v-u := by rw [sub_sub_sub_cancel_right, abs_of_nonneg (sub_nonneg.mpr huv)]
  have middle : max (u-2*(p:ℝ)) 0 ≤ max (v-2*(p:ℝ)) 0 :=
    max_le_max (by linarith) le_rfl
  change (2*max (v-p) 0 - 3*max (v-↑(2*p : ℕ)) 0 + max (v-↑(4*p : ℕ)) 0)/(2*p) -
    (2*max (u-p) 0 - 3*max (u-↑(2*p : ℕ)) 0 + max (u-↑(4*p : ℕ)) 0)/(2*p) ≤ _
  push_cast
  rw [← sub_div]
  calc _ ≤ (3*(v-u))/(2*(p:ℝ)) := by
         apply div_le_div_of_nonneg_right _ (by positivity)
         linarith [bump p, bump (4*p)]
       _ ≤ 6*(v-u)/u := by
         apply (div_le_div_iff₀ (by positivity) hu).mpr
         nlinarith [mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr (le_of_not_ge past))]

/-- On a doubling interval the weighted prime margin can drop by at most 32 per unit.
The bound is uniform in the primes and in the starting point. -/
theorem margin_drop {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (small : v ≤ 2*u) :
    margin u - 32*(v-u) ≤ margin v := by
  let N := ⌊v⌋₊
  have cut : sumTo ⌊u⌋₊ u = sumTo N u := sumTo_extend (Nat.floor_le_floor huv) (Nat.lt_floor_add_one _)
  have dif : sumTo N v - sumTo N u ≤ (6*(v-u)/u)*Chebyshev.theta v := by
    rw [sumTo, sumTo, ← Finset.sum_sub_distrib, Chebyshev.theta_eq_sum_primesLE, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [← mul_sub, mul_comm (6*(v-u)/u)]
    exact mul_le_mul_of_nonneg_left (weight_rise hu huv (Nat.prime_of_mem_primesLE hp).pos)
      (Real.log_natCast_nonneg _)
  have gap : 0 ≤ v-u := sub_nonneg.mpr huv
  have th := Chebyshev.theta_le_log4_mul_x (hu.le.trans huv)
  have log4 : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have th' : Chebyshev.theta v ≤ 4*u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr log4) (hu.le.trans huv)]
  have bound := mul_le_mul_of_nonneg_left th' (show 0 ≤ 6*(v-u)/u by positivity)
  have cancel : (6*(v-u)/u)*(4*u) = 24*(v-u) := by field_simp; ring
  rw [cancel] at bound
  change u/2*Real.log 2-sumTo ⌊u⌋₊ u-32*(v-u) ≤ v/2*Real.log 2-sumTo N v
  rw [cut]
  nlinarith [dif.trans bound, mul_nonneg gap (Real.log_pos (by norm_num : (1:ℝ)<2)).le]

#print axioms margin_drop
end RiemannReduction.PrimeGrid
