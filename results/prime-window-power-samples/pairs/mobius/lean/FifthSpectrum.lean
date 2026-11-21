import BandSpectrum
import PrimeBand

open Complex Filter Topology
namespace RiemannReduction.PrimeGrid
noncomputable section

/-- Contribution of an upper-half-plane zero and its conjugate to the normalized margin. -/
def spectralTerm (j : ℕ) (z : ℂ) : ℝ :=
  (((((j:ℝ)/4 : ℝ) : ℂ) ^ (z-1/2)) * ThetaTransfer.bandMellin 2 z).re

/-- A single zero to the right of the line makes its normalized absolute contribution
grow without bound. Its signed real part may still cancel with the other terms. -/
theorem off_line_term_norm_tends_to_infinity {z : ℂ} (right : 1/2 < z.re) (strip : z.re < 1) :
    Tendsto (fun y : ℝ => ‖(y:ℂ)^(z-1/2)*ThetaTransfer.bandMellin 2 z‖) atTop atTop := by
  have h := ThetaTransfer.bandMellin_ne_zero_in_strip (by norm_num : (1:ℝ) < 2)
    (show 0 < z.re by linarith) strip
  have growth := (tendsto_rpow_atTop (sub_pos.mpr right)).atTop_mul_const (norm_pos_iff.mpr h)
  apply growth.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y pos
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos pos]
  norm_num

private lemma band_norm {z : ℂ} (h : 0 < z.im) :
    ‖ThetaTransfer.bandMellin 2 z‖ ≤
      ((2:ℝ)^z.re+1)*((2:ℝ)^z.re+2)/z.im^2 := by
  have a : z.im ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
  have b : z.im ≤ ‖z-1‖ := by
    simpa using (le_abs_self (z-1).im).trans (Complex.abs_im_le_norm (z-1))
  have normTwo : ‖(2:ℂ)^z‖ = (2:ℝ)^z.re := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  have f : ‖(2:ℂ)^z-1‖ ≤ (2:ℝ)^z.re+1 := by simpa [normTwo] using norm_sub_le ((2:ℂ)^z) 1
  have g : ‖(2:ℂ)^z-2‖ ≤ (2:ℝ)^z.re+2 := by simpa [normTwo] using norm_sub_le ((2:ℂ)^z) 2
  unfold ThetaTransfer.bandMellin
  push_cast
  rw [norm_div,norm_mul,norm_mul]
  apply div_le_div₀ (by positivity) (mul_le_mul f g (norm_nonneg _) (by positivity)) (sq_pos_of_pos h)
  simpa [sq] using mul_le_mul a b h.le (norm_nonneg _)

private lemma neg_term_le {j : ℕ} (hj : 4 < j) {z : ℂ} (hz : 0 < z.im) :
    -spectralTerm j z ≤ ((j:ℝ)/4)^(z.re-1/2) * (((2:ℝ)^z.re+1)*((2:ℝ)^z.re+2)/z.im^2) := by
  have jp : (0:ℝ) < (j:ℝ)/4 := by positivity
  let w := ((((j:ℝ)/4 : ℝ) : ℂ) ^ (z-1/2)) * ThetaTransfer.bandMellin 2 z
  have re : -w.re ≤ ‖w‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  change -w.re ≤ _
  refine re.trans ?_
  dsimp [w]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos jp]
  norm_num only [Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]
  exact mul_le_mul_of_nonneg_left (band_norm hz) (Real.rpow_nonneg jp.le _)

private lemma low_term {j : ℕ} (hj : 4 < j) {z : ℂ} (hz : 0 < z.im) (line : z.re = 1/2) :
    -spectralTerm j z ≤ (4+3*Real.sqrt 2)*(1/z.im^2) := by
  have h := neg_term_le hj hz
  rw [line,sub_self,Real.rpow_zero,one_mul,← Real.sqrt_eq_rpow] at h
  have root := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  convert h using 1
  field_simp
  nlinarith

private lemma high_term {j : ℕ} (hj : 4 < j) {z : ℂ} (hz : 0 < z.im) (strip : z.re ≤ 1) :
    -spectralTerm j z ≤ (6*Real.sqrt j)*(1/z.im^2) := by
  have h := neg_term_le hj hz
  have base : (4:ℝ) ≤ j := by exact_mod_cast hj.le
  have big : 1 ≤ (j:ℝ)/4 := by linarith
  have y := Real.rpow_le_rpow_of_exponent_le big (show z.re-1/2 ≤ 1/2 by linarith)
  rw [← Real.sqrt_eq_rpow,Real.sqrt_div (Nat.cast_nonneg j), show Real.sqrt 4 = 2 by norm_num] at y
  have two := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) strip
  rw [Real.rpow_one] at two
  have num : ((2:ℝ)^z.re+1)*((2:ℝ)^z.re+2) ≤ 12 := by
    calc _ ≤ (2+1:ℝ)*(2+2) := mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
         _ = _ := by norm_num
  apply h.trans
  calc _ ≤ (Real.sqrt j/2)*(12/z.im^2) :=
        mul_le_mul y (div_le_div_of_nonneg_right num (sq_nonneg _)) (by positivity) (by positivity)
       _ = _ := by ring

abbrev checkedHeight : ℝ := 3*10^12

/-- Upper-half-plane zero list, two published mass bounds, the finite zero-height check,
and the one-sided consequence of the weighted explicit formula. The definition records
exactly which analytic facts must be supplied to specialize the finite-range result. -/
structure FifthSpectralData where
  zero : ℕ → ℂ
  positive : ∀ k, 0 < (zero k).im
  strip : ∀ k, (zero k).re ≤ 1
  checked : ∀ k, (zero k).im ≤ checkedHeight → (zero k).re = 1/2
  mass : ∀ n : ℕ, (∑ k ∈ Finset.range n, 1/(zero k).im^2) ≤ 2311/100000
  tail : ∀ n : ℕ, (∑ k ∈ (Finset.range n).filter (fun k => checkedHeight < (zero k).im),
    1/(zero k).im^2) ≤ Real.log checkedHeight/(2*Real.pi*checkedHeight)
  formula : ∀ j : ℕ, 4 < j → ∃ e : ℝ, 0 ≤ e ∧
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, spectralTerm j (zero k)) atTop
      (𝓝 (powerMargin j/Real.sqrt j-e))

private lemma partial_budget (data : FifthSpectralData) {j : ℕ} (hj : 4 < j) (n : ℕ) :
    -(∑ k ∈ Finset.range n, spectralTerm j (data.zero k)) ≤
      (4+3*Real.sqrt 2)*(2311/100000) +
      3*Real.sqrt j*Real.log checkedHeight/(Real.pi*checkedHeight) := by
  classical
  let A := 4+3*Real.sqrt 2
  let B := 6*Real.sqrt j
  let S := (Finset.range n).filter (fun k => checkedHeight < (data.zero k).im)
  let f (k : ℕ) := 1/(data.zero k).im^2
  have step (k : ℕ) : -spectralTerm j (data.zero k) ≤ A*f k +
      (if checkedHeight < (data.zero k).im then B*f k else 0) := by
    split_ifs with high
    · exact (high_term hj (data.positive k) (data.strip k)).trans (le_add_of_nonneg_left (by dsimp [A,f]; positivity))
    · simpa [A,f] using low_term hj (data.positive k) (data.checked k (le_of_not_gt high))
  have s := Finset.sum_le_sum (s := Finset.range n) (fun k _ => step k)
  rw [Finset.sum_neg_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_filter,
    ← Finset.mul_sum] at s
  apply s.trans
  have lo := mul_le_mul_of_nonneg_left (data.mass n) (show 0 ≤ A by dsimp [A]; positivity)
  have hi := mul_le_mul_of_nonneg_left (data.tail n) (show 0 ≤ B by dsimp [B]; positivity)
  unfold f A B at *
  convert add_le_add lo hi using 1
  ring

private lemma budget_below_fifth {j : ℕ} (cap : j ≤ 10^18) :
    (4+3*Real.sqrt 2)*(2311/100000) +
      3*Real.sqrt j*Real.log checkedHeight/(Real.pi*checkedHeight) < 1/5 := by
  have r : Real.sqrt 2 ≤ 1415/1000 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  have s : Real.sqrt j ≤ 10^9 := (Real.sqrt_le_iff).mpr
    ⟨by norm_num,by exact_mod_cast (show j ≤ (10^9)^2 by norm_num at cap ⊢; exact cap)⟩
  have ht : (checkedHeight:ℝ)^2 < (2:ℝ)^83 := by norm_num [checkedHeight]
  have logt := Real.log_lt_log (by norm_num [checkedHeight]) ht
  rw [Real.log_pow,Real.log_pow] at logt
  push_cast at logt
  have l : Real.log checkedHeight < 29 := by linarith [Real.log_two_lt_d9]
  have a : 3*Real.sqrt j*Real.log checkedHeight ≤ 3*(10^9)*29 :=
    mul_le_mul (mul_le_mul_of_nonneg_left s (by norm_num)) l.le
      (Real.log_nonneg (by norm_num [checkedHeight])) (by norm_num)
  have b : 3*Real.sqrt j*Real.log checkedHeight/(Real.pi*checkedHeight) ≤ 29/3100 := by
    apply (div_le_iff₀ (by positivity : 0 < Real.pi*checkedHeight)).mpr
    apply a.trans
    calc (3:ℝ)*10^9*29 = 29/3100*((31/10)*(3*10^12)) := by norm_num
         _ ≤ 29/3100*(Real.pi*checkedHeight) := by
           gcongr
           linarith only [Real.pi_gt_d2]
  linarith

/-- After supplying the published analytic inputs, all integers through 10^18 satisfy
the strict one-fifth inequality, including both endpoints and every doubled prime. -/
theorem fifth_through_ten_pow_eighteen (data : FifthSpectralData) {j : ℕ}
    (hj : 4 < j) (cap : j ≤ 10^18) : -(Real.sqrt j/5) < powerMargin j := by
  obtain ⟨e,ep,h⟩ := data.formula j hj
  have bound := le_of_tendsto h.neg (Filter.Eventually.of_forall (partial_budget data hj))
  have small := budget_below_fifth cap
  have pos : 0 < Real.sqrt j := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have div : -(1/5:ℝ) < powerMargin j/Real.sqrt j := by linarith
  have := (lt_div_iff₀ pos).mp div
  linarith

#print axioms fifth_through_ten_pow_eighteen
#print axioms off_line_term_norm_tends_to_infinity
end
end RiemannReduction.PrimeGrid

namespace RiemannReduction.PrimeGrid

/-- The normalized finite-height bound before choosing a cutoff or a tolerance. -/
theorem normalized_loss_of_spectral_data (data : FifthSpectralData) {j : ℕ} (hj : 4 < j) :
    -(powerMargin j/Real.sqrt j) ≤ (4+3*Real.sqrt 2)*(2311/100000) +
      3*Real.sqrt j*Real.log checkedHeight/(Real.pi*checkedHeight) := by
  obtain ⟨e,ep,h⟩ := data.formula j hj
  have bound := le_of_tendsto h.neg (Filter.Eventually.of_forall (partial_budget data hj))
  linarith

/-- If every listed point lies on the critical line, the adverse contribution is
bounded by the total inverse-square mass at every scale. -/
theorem fifth_at_every_scale_of_line (data : FifthSpectralData)
    (line : ∀ i, (data.zero i).re = 1/2) {j : ℕ} (hj : 4 < j) :
    -(Real.sqrt j/5) < powerMargin j := by
  let A := 4+3*Real.sqrt 2
  have partialBound (n : ℕ) :
      -(∑ i ∈ Finset.range n, spectralTerm j (data.zero i)) ≤ A*(2311/100000) := by
    have h := Finset.sum_le_sum (s := Finset.range n)
      (fun i _ => low_term hj (data.positive i) (line i))
    rw [Finset.sum_neg_distrib,← Finset.mul_sum] at h
    exact h.trans (mul_le_mul_of_nonneg_left (data.mass n) (by positivity))
  obtain ⟨e,ep,h⟩ := data.formula j hj
  have bound := le_of_tendsto h.neg (Filter.Eventually.of_forall partialBound)
  have mass : A*(2311/100000) < 1/5 := by
    simpa only [A,Nat.cast_zero,Real.sqrt_zero,mul_zero,zero_mul,zero_div,add_zero] using
      (budget_below_fifth (j := 0) (by norm_num))
  have pos : 0 < Real.sqrt j := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have div : -(1/5:ℝ) < powerMargin j/Real.sqrt j := by linarith
  linarith [(lt_div_iff₀ pos).mp div]

#print axioms normalized_loss_of_spectral_data
#print axioms fifth_at_every_scale_of_line
end RiemannReduction.PrimeGrid
