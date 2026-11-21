import Mathlib

namespace ShortBlock.ShiftParity

open scoped BigOperators

/-- The two adjacent dyadic translates on the falling and rising branches. -/
theorem adjacent_tent_weights (t : ℝ) (ht : 0 < t) :
    (1 / t - 1) + (2 - 1 / (2 * (t / 2))) = 1 := by
  field_simp
  ring

/-- Sum the discrepancy over both orientations of a pair from opposite classes.
The two index sets in the application are the even and odd members of the support. -/
theorem ordered_cross_sum {ι : Type*} (e o : Finset ι) (a w : ι → ℝ) :
    (∑ i ∈ e, ∑ j ∈ o, (a i * a j + w i * w j)) +
      (∑ j ∈ o, ∑ i ∈ e, (a j * a i + w j * w i)) =
    2 * ((∑ i ∈ e, a i) * (∑ j ∈ o, a j) +
      (∑ i ∈ e, w i) * (∑ j ∈ o, w j)) := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The normalized odd-shift discrepancy determines the full linear sum. -/
theorem recover_linear_sum (x r u s e o : ℝ) (hu : u ≠ 0)
    (hr : x * r = 2 * (u * (s - u) + e * o)) :
    u + (x * r / 2 - e * o) / u = s := by
  rw [hr]
  field_simp
  ring

/-- A uniform bound on the relative prime-sum error controls its block square
by the absolute first moment on the same set of samples. -/
theorem square_sum_of_relative_bound {ι : Type*} (samples : Finset ι)
    (x s : ι → ℝ) (d : ℝ) (hx : ∀ i ∈ samples, 0 < x i)
    (hs : ∀ i ∈ samples, |s i| ≤ d * x i) :
    ∑ i ∈ samples, (s i)^2 / x i ≤ d * ∑ i ∈ samples, |s i| := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply (div_le_iff₀ (hx i hi)).2
  calc
    (s i)^2 = |s i| * |s i| := by rw [← sq, sq_abs]
    _ ≤ (d * x i) * |s i| := mul_le_mul_of_nonneg_right (hs i hi) (abs_nonneg _)
    _ = (d * |s i|) * x i := by ring

/-- Transfer a certified error on an odd-shift estimate to the squared sum. -/
theorem square_error_of_absolute_error (a b err : ℝ) (h : |a - b| ≤ err) :
    |a^2 - b^2| ≤ err * (2 * |b| + err) := by
  have hplus : |a + b| ≤ 2 * |b| + err := calc
    |a + b| = |(a - b) + (b + b)| := by congr 1; ring
    _ ≤ |a - b| + |b + b| := abs_add_le _ _
    _ ≤ err + (|b| + |b|) := add_le_add h (abs_add_le _ _)
    _ = 2 * |b| + err := by ring
  calc
    |a^2 - b^2| = |a-b| * |a+b| := by rw [← abs_mul]; congr 1; ring
    _ ≤ err * (2 * |b| + err) :=
      mul_le_mul h hplus (abs_nonneg _) ((abs_nonneg _).trans h)

/-- The normalized energy error at one scale, with the constants from (A). -/
theorem proxy_square_error (x s z : ℝ) (hx : 8 ≤ x) (hs : |s| ≤ 3*x)
    (hz : |z-s| ≤ 330/x) : |z^2/x-s^2/x| ≤ 3700/x := by
  have hx0 : 0 < x := by linarith
  have hx2 : (8:ℝ)^2 ≤ x^2 := sq_le_sq' (by linarith) hx
  rw [← sub_div, abs_div, abs_of_pos hx0]
  apply div_le_div_of_nonneg_right _ hx0.le
  calc
    |z^2-s^2| ≤ (330/x) * (2*|s|+330/x) := square_error_of_absolute_error z s _ hz
    _ ≤ (330/x) * (2*(3*x)+330/x) := by gcongr
    _ = 1980 + 108900/x^2 := by field_simp; ring
    _ ≤ 3700 := by
      have h : (108900:ℝ)/x^2 ≤ 1720 := (div_le_iff₀ (by positivity)).2 (by nlinarith)
      linarith

/-- A telescoping majorant for reciprocal squares on a consecutive block. -/
theorem reciprocal_square_sum (k : ℝ) (hk : 1 < k) (n : ℕ) :
    ∑ j ∈ Finset.range n, 1/(k+(j:ℝ))^2 ≤ 1/(k-1) - 1/(k+(n:ℝ)-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 1 < k+(n:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have step : 1/(k+(n:ℝ))^2 ≤ 1/(k+(n:ℝ)-1) - 1/(k+(n:ℝ)) := by
      set t := k+(n:ℝ)
      have ht : 0 < t := by linarith
      have hpred : 0 < t-1 := by linarith
      calc
        1/t^2 ≤ 1/((t-1)*t) := one_div_le_one_div_of_le (mul_pos hpred ht) (by nlinarith)
        _ = 1/(t-1)-1/t := by field_simp; ring
    rw [Finset.sum_range_succ, Nat.cast_succ]
    rw [show k+((n:ℝ)+1)-1 = k+n by ring]
    linarith

/-- A pointwise error at the scales (k+j)^2 gives the block tolerance in (A).
Here the two input functions already include the normalization by scale. -/
theorem proxy_block_error (k : ℝ) (hk : 1 < k) (n : ℕ)
    (estimate observed : ℕ → ℝ)
    (h : ∀ j ∈ Finset.range n, |estimate j - observed j| ≤ 3700/(k+(j:ℝ))^2) :
    |(∑ j ∈ Finset.range n, estimate j)/(n:ℝ) -
      (∑ j ∈ Finset.range n, observed j)/(n:ℝ)| ≤ 3700/((k-1)*(n:ℝ)) := by
  have start : 0 < k+(n:ℝ)-1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have total : ∑ j ∈ Finset.range n, 1/(k+(j:ℝ))^2 ≤ 1/(k-1) := by
    linarith [reciprocal_square_sum k hk n, one_div_pos.mpr start]
  have error : |∑ j ∈ Finset.range n, (estimate j - observed j)| ≤ 3700/(k-1) := calc
    _ ≤ ∑ j ∈ Finset.range n, |estimate j - observed j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, 3700/(k+(j:ℝ))^2 := Finset.sum_le_sum h
    _ = 3700 * ∑ j ∈ Finset.range n, 1/(k+(j:ℝ))^2 := by simp [Finset.mul_sum, div_eq_mul_inv]
    _ ≤ 3700 * (1/(k-1)) := mul_le_mul_of_nonneg_left total (by norm_num)
    _ = _ := by ring
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
    ← div_div]
  exact div_le_div_of_nonneg_right error (Nat.cast_nonneg _)

#print axioms adjacent_tent_weights
#print axioms ordered_cross_sum
#print axioms recover_linear_sum
#print axioms square_sum_of_relative_bound
#print axioms square_error_of_absolute_error
#print axioms proxy_square_error
#print axioms reciprocal_square_sum
#print axioms proxy_block_error

end ShortBlock.ShiftParity
