import MobiusBlocks
import CenteredPrimeRamps
import Formalism.ZeroFreeRegion.LogDerivRegion

open Finset Filter
open scoped ArithmeticFunction.vonMangoldt

namespace RiemannReduction.DivisorBand
noncomputable section

/-- A bound for the complete signed sum, including every sign and every root index. -/
theorem whole_tail_pnt : ∃ b > (0:ℝ), ∃ M > (0:ℝ), ∀ k : ℕ, 108^2 ≤ k →
    let budget := M*(k:ℝ)^2*Real.exp (-b*Real.sqrt (Real.log k))
    |PrimeGrid.powerMargin (k^2)| ≤ budget ∧ |largeDivisorSum k| ≤ budget ∧
      |unpairedTail k (k*k.sqrt)| ≤ budget := by
  obtain ⟨c₀,A,cp,est⟩ := Formalism.ZF.gzPNT
  let b := min c₀ 1
  have bp : 0 < b := lt_min cp one_pos
  have bc : b ≤ c₀ := min_le_left _ _
  have b1 : b ≤ 1 := min_le_right _ _
  refine ⟨b,bp,6*|A|+117,by positivity,?_⟩
  intro k hk
  let x := (k:ℝ)^2
  let E := Real.exp (-b*Real.sqrt (Real.log k))
  have k4 : (4:ℝ) ≤ k := by exact_mod_cast (show 4 ≤ k by norm_num at hk; omega)
  have kp : 0 < (k:ℝ) := by linarith
  have rem := remainder_margin_comparison hk
  have tails := tail_margin_comparison (Nat.cast_pos.mp kp)
  have size : 4*(k:ℝ) ≤ x := mul_le_mul_of_nonneg_right k4 kp.le |>.trans_eq (by dsimp [x]; ring)
  have x0 : 0 ≤ x := sq_nonneg _
  have e0 : 0 ≤ E := (Real.exp_pos _).le
  have ramp {t : ℝ} (lo : (k:ℝ) ≤ t) (hi : t ≤ x) : |Formalism.Gz t| ≤ |A| * x*E := by
    have ht : 2 ≤ t := by linarith
    have l := Real.sqrt_le_sqrt (Real.log_le_log kp lo)
    have exponent := mul_le_mul bc l (Real.sqrt_nonneg _) cp.le
    have val : Real.exp (-c₀*Real.sqrt (Real.log t)) ≤ E :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact (est t ht).trans (mul_le_mul
      (mul_le_mul (le_abs_self A) hi (by linarith) (abs_nonneg _)) val (Real.exp_pos _).le
      (mul_nonneg (abs_nonneg _) x0))
  have r1 := abs_le.mp (ramp (show (k:ℝ) ≤ x by linarith) le_rfl)
  have r2 := abs_le.mp (ramp (show (k:ℝ) ≤ x/2 by linarith) (by linarith : x/2 ≤ x))
  have r4 := abs_le.mp (ramp (show (k:ℝ) ≤ x/4 by linarith) (by linarith : x/4 ≤ x))
  have id := D_nat (k^2)
  rw [Nat.cast_pow] at id
  change D x = PrimeGrid.powerMargin (k^2) at id
  rw [deficit_eq_gz (by linarith : 0 < x)] at id
  have L : 1 ≤ Real.log k := by
    have four := Real.log_le_log (by norm_num : (0:ℝ)<4) k4
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at four
    push_cast at four
    linarith [Real.log_two_gt_d9]
  have rs := Real.sq_sqrt (show 0 ≤ Real.log k by linarith)
  have rlo : 1 ≤ Real.sqrt (Real.log k) := Real.one_le_sqrt.mpr L
  have le : b*Real.sqrt (Real.log k) ≤ Real.log k := by
    nlinarith [mul_le_mul_of_nonneg_right b1 (Real.sqrt_nonneg (Real.log k)),
      mul_le_mul_of_nonneg_right rlo (Real.sqrt_nonneg (Real.log k))]
  have one : 1 ≤ (k:ℝ)*E := by
    calc 1 ≤ Real.exp (Real.log k + (-b*Real.sqrt (Real.log k))) :=
            Real.one_le_exp (by linarith)
         _ = (k:ℝ)*E := by rw [Real.exp_add, Real.exp_log kp]
  have absorb : (k:ℝ) ≤ x*E := by dsimp [x]; nlinarith [mul_le_mul_of_nonneg_left one kp.le]
  change |PrimeGrid.powerMargin (k^2)| ≤ (6*|A|+117)*x*E ∧ _ ∧ _
  change _ ∧ |largeDivisorSum k| ≤ (6*|A|+117)*x*E ∧ |unpairedTail k (k*k.sqrt)| ≤ (6*|A|+117)*x*E
  simp only [abs_le]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> nlinarith [mul_nonneg x0 e0]

/-- The unconditional allowance divided by k still diverges for every fixed b. -/
theorem pnt_allowance_per_root_grows (b : ℝ) :
    Tendsto (fun k : ℕ => (k:ℝ)*Real.exp (-b*Real.sqrt (Real.log k))) atTop atTop := by
  have cast := tendsto_natCast_atTop_atTop (R:=ℝ)
  apply tendsto_atTop_mono' atTop _ (Real.tendsto_sqrt_atTop.comp cast)
  filter_upwards [eventually_ge_atTop (1:ℕ),
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp cast)).eventually_ge_atTop (2*b)]
    with k hk big
  have k1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have kp : (0:ℝ) < k := by linarith
  have rs := Real.sq_sqrt (Real.log_nonneg k1)
  change 2*b ≤ Real.sqrt (Real.log k) at big
  calc Real.sqrt (k:ℝ) = Real.exp (Real.log k/2) := by rw [Real.exp_half,Real.exp_log kp]
       _ ≤ Real.exp (Real.log k+(-b*Real.sqrt (Real.log k))) := by
         apply Real.exp_le_exp.mpr
         nlinarith [mul_le_mul_of_nonneg_right big (Real.sqrt_nonneg (Real.log k))]
       _ = _ := by rw [Real.exp_add,Real.exp_log kp]

#print axioms whole_tail_pnt
#print axioms pnt_allowance_per_root_grows
end
end RiemannReduction.DivisorBand
