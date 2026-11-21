import Mathlib

open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace ThetaTransfer

/-- Write t = y/n. Positive weights have y < n < 4y. -/
def tent (t : ℝ) : ℝ :=
  max (4 * t - 1) 0 - 3 * max (2 * t - 1) 0 + 2 * max (t - 1) 0

theorem tent_pieces (t : ℝ) :
    tent t = if 1 ≤ t then 0 else if 1 / 2 ≤ t then 2 * (1 - t)
      else if 1 / 4 ≤ t then 4 * t - 1 else 0 := by
  unfold tent
  split_ifs <;> grind [max_def]

theorem tent_nonneg (t : ℝ) : 0 ≤ tent t := by
  rw [tent_pieces]
  split_ifs <;> linarith

theorem tent_le_one (t : ℝ) : tent t ≤ 1 := by
  rw [tent_pieces]
  split_ifs <;> linarith

def primePowerSum (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊4 * y⌋₊ + 1), Λ n * tent (y / n)

def primeSum (y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range (⌊4 * y⌋₊ + 1)).filter Nat.Prime, Real.log n * tent (y / n)

theorem primeSum_le_primePowerSum (y : ℝ) : primeSum y ≤ primePowerSum y := by
  unfold primeSum primePowerSum
  calc
    _ = ∑ n ∈ (Finset.range (⌊4 * y⌋₊ + 1)).filter Nat.Prime, Λ n * tent (y / n) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg) (tent_nonneg _))

theorem primePowerGap_le (y : ℝ) :
    primePowerSum y - primeSum y ≤ Chebyshev.psi (4*y) - Chebyshev.theta (4*y) := by
  rw [primePowerSum, primeSum, Nat.range_succ_eq_Icc_zero, Chebyshev.psi_eq_sum_Icc,
    Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro n _
  by_cases h : Nat.Prime n
  · simp [h, ArithmeticFunction.vonMangoldt_apply_prime h]
  · simpa [h] using mul_le_of_le_one_right (ArithmeticFunction.vonMangoldt_nonneg (n := n))
      (tent_le_one (y / n))

end ThetaTransfer

namespace RiemannReduction.PrimeGrid

/-- The centered prime-power sum, evaluated at integer upper endpoint j. -/
noncomputable def powerMargin (j : ℕ) : ℝ :=
  (j:ℝ)/2 * Real.log 2 - ThetaTransfer.primePowerSum ((j:ℝ)/4)

end RiemannReduction.PrimeGrid
