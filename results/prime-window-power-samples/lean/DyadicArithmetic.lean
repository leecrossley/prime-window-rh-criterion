import PrimeBand
import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily

open scoped ArithmeticFunction.vonMangoldt
open Complex

noncomputable section
namespace ThetaTransfer

private theorem ramp_extend {x z : ℝ} (hxz : x ≤ z) :
    (Deduction.ramp (fun _ => 1) x).re =
      ∑ n ∈ Finset.range (⌊z⌋₊ + 1), Λ n * max (x / n - 1) 0 := by
  simp [Deduction.ramp, Complex.re_sum]
  apply Finset.sum_subset_zero_on_sdiff
  · exact Finset.range_subset_range.mpr (by gcongr)
  · intro i hi
    have hi' := (Finset.mem_sdiff.mp hi).2
    simp only [Finset.mem_range, not_lt] at hi'
    have hi0 : 0 < i := by omega
    have hxi : x < (i : ℝ) :=
      (Nat.floor_lt' (Nat.ne_of_gt hi0)).mp (by omega)
    rw [max_eq_right (by
      have := (div_le_one (Nat.cast_pos.mpr hi0 : 0 < (i : ℝ))).mpr hxi.le
      linarith)]
    simp
  · intros
    rfl

theorem primePowerSum_eq_ramps {y : ℝ} (hy : 0 < y) :
    primePowerSum y = (Deduction.ramp (fun _ => 1) (4*y)).re
      - 3 * (Deduction.ramp (fun _ => 1) (2*y)).re
      + 2 * (Deduction.ramp (fun _ => 1) y).re := by
  rw [ramp_extend (z := 4*y) le_rfl, ramp_extend (x := 2*y) (z := 4*y) (by linarith),
    ramp_extend (x := y) (z := 4*y) (by linarith)]
  simp only [primePowerSum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [tent, mul_div_assoc]
  ring

theorem deficit_eq_centered_ramps {y : ℝ} (hy : 0 < y) :
    2 * Real.log 2 * y - primePowerSum y =
      -Deduction.G (4*y) + 3 * Deduction.G (2*y) - 2 * Deduction.G y := by
  rw [primePowerSum_eq_ramps hy]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  unfold Deduction.G
  rw [Real.log_mul (by norm_num) hy.ne', Real.log_mul (by norm_num) hy.ne', h4]
  ring

end ThetaTransfer
