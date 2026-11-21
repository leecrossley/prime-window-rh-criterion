import FiniteQuarticBudget

open Finset
namespace RiemannReduction.DivisorBand.FourthMass

/-- Include every integer, using the two published finite-height ranges for D. -/
theorem finite_hundred_blocks (env : finiteDeficitEnvelope)
    (small : ∀ k : ℕ, 32 ≤ k → k < 10^8 → |D ((k:ℝ)^2)| ≤ k)
    {K : ℕ} (low : 32 ≤ K) (high : K ≤ 57*10^11) :
    ∀ k ∈ Icc K (K^2), -100*(k:ℝ) ≤ D ((k:ℝ)^2) := by
  intro k hk
  obtain ⟨left,right⟩ := mem_Icc.mp hk
  have kp : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  by_cases early : k < 10^8
  · have h := (abs_le.mp (small k (low.trans left) early)).1
    linarith
  have cap := right.trans (Nat.pow_le_pow_left high 2)
  have cr : (k:ℝ) ≤ (57*10^11)^2 := by exact_mod_cast cap
  have h := (abs_le.mp (env k (by omega) (cap.trans (by norm_num)))).1
  have cost : (3/10:ℝ)+(55/2)*k/(3*10^12)^2 ≤ 100  := by
    calc _ ≤ 3/10+(55/2)*(((57*10^11)^2):ℝ)/(3*10^12)^2 := by gcongr
         _ ≤ (100:ℝ) := by norm_num
  linarith [mul_le_mul_of_nonneg_right cost kp]

end RiemannReduction.DivisorBand.FourthMass
