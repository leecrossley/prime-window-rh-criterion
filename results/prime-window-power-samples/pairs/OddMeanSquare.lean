import Mathlib

namespace ShortBlock.OddMeanSquare

open scoped BigOperators

/-- The finite symmetric row estimate used on the absolute Gram kernel.
Repeated ordinates may be represented by distinct indices. -/
theorem symmetric_row_bound {ι : Type*} (s : Finset ι) (a r : ι → ℝ) (w : ι → ι → ℝ)
    (nonneg : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ w i j)
    (symm : ∀ i ∈ s, ∀ j ∈ s, w i j = w j i)
    (rows : ∀ i ∈ s, ∑ j ∈ s, w i j ≤ r i) :
    ∑ i ∈ s, ∑ j ∈ s, w i j * a i * a j ≤ ∑ i ∈ s, r i * (a i)^2 := by
  have bound : ∑ i ∈ s, ∑ j ∈ s, 2 * (w i j * a i * a j) ≤
      ∑ i ∈ s, ∑ j ∈ s, (w i j * (a i)^2 + w j i * (a j)^2) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    rw [← symm i hi j hj]
    nlinarith [mul_nonneg (nonneg i hi j hj) (sq_nonneg (a i - a j))]
  have swap : (∑ i ∈ s, ∑ j ∈ s, w j i * (a j)^2) =
      ∑ i ∈ s, ∑ j ∈ s, w i j * (a i)^2 := Finset.sum_comm
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at bound
  rw [swap] at bound
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, w i j * (a i)^2 := by linarith
    _ ≤ ∑ i ∈ s, r i * (a i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (rows i hi) (sq_nonneg _)

/-- Dominate a row of the Gram kernel by a term of the log derivative of xi. -/
theorem strip_row_comparison (k d c v : ℝ) (hk : 0 < k) (hd : 0 < d)
    (hzero : d ≤ c*k^2) (hinfty : 1 ≤ 4*c*d) :
    1/(k^2 + 4*v^2) ≤ c*(d/(d^2+v^2)) := by
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hzero hd.le,
    mul_le_mul_of_nonneg_right hinfty (sq_nonneg v)]

#print axioms symmetric_row_bound
#print axioms strip_row_comparison

end ShortBlock.OddMeanSquare
