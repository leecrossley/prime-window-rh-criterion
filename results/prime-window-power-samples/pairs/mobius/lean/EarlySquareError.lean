import EarlySmallDivisors
import FinePairOffsets

open Finset
namespace RiemannReduction.DivisorBand
noncomputable section

theorem early_deficit_error_explicit {k : ℕ} (late : 10^8 ≤ k) :
    |D ((k:ℝ)^2) - unpairedTail k (k*k.sqrt)| ≤ (47/24)*(k:ℝ)+1 := by
  have large : (10^8 : ℝ) ≤ k := by exact_mod_cast late
  have kp : 0 < (k:ℝ) := by linarith
  have old : 108^2 ≤ k := by omega
  have c0 : 1/3 ≤ c := by unfold c; linarith [Real.log_two_gt_d9]
  have c1 : c ≤ 7/20 := by unfold c; linarith [Real.log_two_lt_d9]
  have slope : mainSlope = c*(Real.eulerMascheroniConstant+1-c) := by
    unfold mainSlope c logMoment
    ring
  have lowSlope : 0 ≤ mainSlope := by
    rw [slope]
    exact mul_nonneg (by linarith) (by linarith [Real.one_half_lt_eulerMascheroniConstant])
  have highSlope : mainSlope ≤ 1 := by
    rw [slope]
    calc _ ≤ (7/20:ℝ)*(4/3) := mul_le_mul c1 (by linarith [Real.eulerMascheroniConstant_lt_two_thirds])
            (by linarith [Real.one_half_lt_eulerMascheroniConstant]) (by norm_num)
         _ ≤ _ := by norm_num
  have small := abs_le.mp (EarlySmall.small_divisors_cost_five_sixths late)
  have pair := abs_le.mp (FinePair.paired_cost_nine_eighths old)
  have id := D_nat (k^2)
  rw [Nat.cast_pow] at id
  rw [← id] at small
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem early_deficit_error_two {k : ℕ} (late : 10^8 ≤ k) :
    |D ((k:ℝ)^2) - unpairedTail k (k*k.sqrt)| ≤ 2*(k:ℝ) := by
  have large : (10^8 : ℝ) ≤ k := by exact_mod_cast late
  exact (early_deficit_error_explicit late).trans (by linarith)

end
end RiemannReduction.DivisorBand
