import EarlySquareError
import FourthSignedCriterion
import Mathlib.Algebra.BigOperators.Intervals

open Finset
namespace RiemannReduction.DivisorBand.FourthMass
noncomputable section

private theorem block_harmonic_sharp {m : ℕ} (mp : 0 < m) :
    ∑ n ∈ Icc m (m^2), (n:ℝ)⁻¹ ≤ (m:ℝ)⁻¹ + Real.log m := by
  have mm : m ≤ m^2 := Nat.le_self_pow (by decide) m
  have upper := Real.strictAnti_eulerMascheroniSeq'.antitone mm
  simp only [Real.eulerMascheroniSeq', if_neg (pow_ne_zero 2 mp.ne'), if_neg mp.ne',
    Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at upper
  have harmonic_identity (a : ℕ) : (harmonic a : ℝ) = ∑ n ∈ Ioc 0 a, (n:ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    congr 1
  rw [harmonic_identity, harmonic_identity, ← sum_Ioc_consecutive (fun n : ℕ => (n:ℝ)⁻¹) (Nat.zero_le m) mm] at upper
  rw [Icc_eq_cons_Ioc mm, sum_cons]
  linarith

private theorem sum_indices (m : ℕ) :
    ∑ n ∈ Icc m (m^2), (n:ℝ) ≤ ((m:ℝ)^4+(m:ℝ)^2)/2 := by
  let z := m^2
  have h := sum_range_id_mul_two (z+1)
  rw [Nat.add_sub_cancel] at h
  have hr : (∑ i ∈ range (z+1), (i:ℝ))*2 = ((z:ℝ)+1)*z := by
    have equality := congrArg (fun j : ℕ => (j:ℝ)) h
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_sum] using equality
  have sub : Icc m (m^2) ⊆ range (z+1) := by
    intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hn).2)
  have less := sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => (n:ℝ)) sub (fun i _ _ => Nat.cast_nonneg i)
  dsimp [z] at hr less
  push_cast at hr
  linarith

/-- The written finite-height estimate in the accompanying note supplies this premise. -/
def finiteDeficitEnvelope : Prop :=
  ∀ k : ℕ, 10^8 ≤ k → k ≤ 10^28 →
    |D ((k:ℝ)^2)| ≤ (3/10 + (55/2)*(k:ℝ)/(3*10^12)^2)*k

private theorem sample_majorant (env : finiteDeficitEnvelope) (s : ℝ) (sgn : s=1 ∨ s= -1)
    {n : ℕ} (lo : 10^4 ≤ n) (hi : n ≤ (2*10^6)^2) :
    max (signedRemainder s n) 0/(n:ℝ)^3 ≤ (23/10)*(n:ℝ)⁻¹+((55/2)/(3*10^12)^2)*(n:ℝ) := by
  have lower : 10^8 ≤ n^2 := (by norm_num : 10^8 = (10^4)^2) ▸ Nat.pow_le_pow_left lo 2
  have upper : n^2 ≤ 10^28 := (Nat.pow_le_pow_left hi 2).trans (by norm_num)
  have est := env (n^2) lower upper
  have diff := early_deficit_error_two lower
  change |D (((n^2:ℕ):ℝ)^2) - remainder n| ≤ 2*((n^2:ℕ):ℝ) at diff
  rw [Nat.cast_pow] at est diff
  have npos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have size : |remainder n| ≤ (3/10+(55/2)*(n:ℝ)^2/(3*10^12)^2)*n^2+2*(n:ℝ)^2 := by
    have tri := abs_sub_le (remainder n) (D (((n:ℝ)^2)^2)) 0
    rw [sub_zero,sub_zero,abs_sub_comm (remainder n)] at tri
    linarith
  have clipped : max (signedRemainder s n) 0 ≤ |remainder n| := by
    apply max_le _ (abs_nonneg _)
    rcases sgn with rfl | rfl
    · simpa [signedRemainder] using le_abs_self (remainder n)
    · simpa [signedRemainder] using neg_le_abs (remainder n)
  apply (div_le_iff₀ (pow_pos npos 3)).mpr
  apply (clipped.trans size).trans_eq
  field_simp
  ring

/-- A direct finite logarithmic budget for either sign of the actual fourth-power
    remainder. The analytic envelope is proved on paper using finite zero verification. -/
theorem finite_quartic_budget (env : finiteDeficitEnvelope) (s : ℝ) (sgn : s=1 ∨ s= -1)
    {m : ℕ} (lo : 10^4 ≤ m) (hi : m ≤ 2*10^6) :
    mass (signedRemainder s) m ≤ 2*(1+2*Real.log m) := by
  have pos : 0 < m := by omega
  have mr : (10^4:ℝ) ≤ m := by exact_mod_cast lo
  have cap : (m:ℝ) ≤ 2*10^6 := by exact_mod_cast hi
  have mpos : (0:ℝ) < m := Nat.cast_pos.mpr pos
  have lin := block_harmonic_sharp pos
  have tri := sum_indices m
  have allTerms := sum_le_sum (s:=Icc m (m^2)) (fun n hn =>
    sample_majorant env s sgn (lo.trans (mem_Icc.mp hn).1)
      ((mem_Icc.mp hn).2.trans (Nat.pow_le_pow_left hi 2)))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at allTerms
  have cost := mul_le_mul_of_nonneg_left tri (by norm_num : (0:ℝ) ≤ (55/2)/(3*10^12)^2)
  have logTerm := mul_le_mul_of_nonneg_left lin (by norm_num : (0:ℝ) ≤ 23/10)
  have invbound : (m:ℝ)⁻¹ ≤ 1/10000 := (inv_le_comm₀ mpos (by norm_num)).mpr (by norm_num at mr ⊢; linarith)
  have lg0 := Real.log_nonneg (by linarith : (1:ℝ) ≤ m)
  change (∑ n ∈ Icc m (m^2), _) ≤ _
  apply allTerms.trans
  by_cases half : (m:ℝ) ≤ 10^6
  · have p4 := pow_le_pow_left₀ mpos.le half 4
    have p2 := pow_le_pow_left₀ mpos.le half 2
    norm_num at cost p4 p2 logTerm invbound ⊢
    linarith
  · have p4 := pow_le_pow_left₀ mpos.le cap 4
    have p2 := pow_le_pow_left₀ mpos.le cap 2
    have lg := Real.log_le_log (by norm_num : (0:ℝ)<(10:ℝ)^6) (le_of_not_ge half)
    rw [Real.log_pow,Real.log_ten_eq] at lg
    norm_num at cost p4 p2 logTerm invbound lg ⊢
    linarith [Real.log_two_gt_d9,Real.log_five_gt_d9]

end
end RiemannReduction.DivisorBand.FourthMass
