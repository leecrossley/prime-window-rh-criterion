import EarlyBandQuadrature
import MobiusTail

open Finset ArithmeticFunction
namespace RiemannReduction.DivisorBand.EarlySmall
noncomputable section

private lemma harmonic_floor_error {x : ℝ} (large : 10^8 ≤ x) :
    |x*((harmonic ⌊x⌋₊:ℝ)-Real.log x-Real.eulerMascheroniConstant)| ≤ 101/100 := by
  have hx : 1 ≤ x := by linarith
  let n := ⌊x⌋₊
  have n1 : 1 ≤ n := Nat.le_floor (by simpa using hx)
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr n1
  have one : (1:ℝ) ≤ n := by exact_mod_cast n1
  have le : (n:ℝ) ≤ x := Nat.floor_le (by linarith)
  have lt : x < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have lo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have up := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [Real.eulerMascheroniSeq] at lo
  rw [Real.eulerMascheroniSeq',if_neg (by omega : n ≠ 0)] at up
  have loglo := Real.log_le_log np le
  have loghi := Real.log_le_log (by linarith : 0<x) lt.le
  have gap : Real.log ((n:ℝ)+1)-Real.log n ≤ 1/n := by
    rw [← Real.log_div (by positivity) np.ne']
    apply (Real.log_le_sub_one_of_pos (by positivity)).trans
    field_simp; linarith
  have err : |(harmonic n:ℝ)-Real.log x-Real.eulerMascheroniConstant| ≤ 1/n :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ x)]
  exact (mul_le_mul_of_nonneg_left err (by linarith)).trans (by
    rw [← mul_div_assoc,mul_one]
    have r100 : (100 : ℝ) ≤ x := (by norm_num : (100 : ℝ) ≤ 10^8).trans large
    have bigN : (100 : ℕ) ≤ n := Nat.le_floor (by exact_mod_cast r100)
    have bigR : (100 : ℝ) ≤ n := by exact_mod_cast bigN
    exact (div_le_iff₀ np).mpr (by linarith))

theorem residual_five_sixths {x : ℝ} (large : 10^8 ≤ x) : |residual mainSlope x| ≤ 5/6 := by
  have clo : 1/3 ≤ c := by unfold c; linarith [Real.log_two_gt_d9]
  have chi : c ≤ 7/20 := by unfold c; linarith [Real.log_two_lt_d9]
  have slope : mainSlope = c*(Real.eulerMascheroniConstant+1-c) := by
    unfold mainSlope c logMoment
    ring
  have apos : 0 ≤ mainSlope := by
    rw [slope]
    exact mul_nonneg (by linarith) (by linarith [Real.one_half_lt_eulerMascheroniConstant])
  have amax : mainSlope ≤ 7/15 := by
    rw [slope]
    calc _ ≤ (7/20 : ℝ)*(4/3) := mul_le_mul chi (by linarith [Real.eulerMascheroniConstant_lt_two_thirds])
           (by linarith [Real.one_half_lt_eulerMascheroniConstant]) (by norm_num)
         _ = _ := by norm_num
  have hf := Nat.floor_le (show 0 ≤ x by linarith)
  have ht := Nat.lt_floor_add_one x
  have frac : 0 ≤ mainSlope*(x-⌊x⌋₊) ∧ mainSlope*(x-⌊x⌋₊) ≤ 7/15 :=
    ⟨mul_nonneg apos (by linarith), (mul_le_of_le_one_right apos (by linarith)).trans amax⟩
  have harmonicError := harmonic_floor_error large
  have small : |c*(x*((harmonic ⌊x⌋₊:ℝ)-Real.log x-Real.eulerMascheroniConstant))| ≤
      (7/20)*(101/100) := by
    rw [abs_mul,abs_of_nonneg (show 0 ≤ c by linarith)]
    exact mul_le_mul chi harmonicError (abs_nonneg _) (by norm_num)
  have quad := EarlyQuadrature.log_band_error_hundredth large
  have split : residual mainSlope x =
      c*(x*((harmonic ⌊x⌋₊:ℝ)-Real.log x-Real.eulerMascheroniConstant)) -
      (dilate ArithmeticFunction.log window x-(c*x*Real.log x+logMoment*x)) +
      mainSlope*(x-⌊x⌋₊) := by unfold residual mainSlope; ring
  rw [split]
  simp only [abs_le] at small quad ⊢
  constructor <;> linarith

theorem small_divisors_cost_five_sixths {k : ℕ} (late : 10^8 ≤ k) :
    |PrimeGrid.powerMargin (k^2) - mainSlope - largeDivisorSum k| ≤ (5/6)*k := by
  have hk : 0 < k := by omega
  have large : (10^8 : ℝ) ≤ k := by exact_mod_cast late
  have kk : k ≤ k^2 := Nat.le_self_pow (by decide) k
  have k2 : (1:ℝ) ≤ (k:ℝ)^2 := by exact_mod_cast (show 1 ≤ k^2 by omega)
  have id := moebius_reconstruction mainSlope k2
  have natD := D_nat (k^2)
  rw [Nat.cast_pow] at natD
  rw [natD,dilate,← Nat.cast_pow, Nat.floor_natCast] at id
  have eq : Icc 1 (k^2) = Ioc 0 (k^2) := by ext d; simp only [mem_Icc,mem_Ioc]; omega
  rw [eq,Nat.cast_pow] at id
  change PrimeGrid.powerMargin (k^2) = mainSlope + ∑ d ∈ Ioc 0 (k^2), tailTerm k d at id
  rw [←sum_Ioc_consecutive (tailTerm k) (Nat.zero_le k) kk] at id
  have split : PrimeGrid.powerMargin (k^2)-mainSlope-largeDivisorSum k = ∑ d ∈ Ioc 0 k, tailTerm k d := by
    change _-_- (∑ d ∈ Ioc k (k^2),tailTerm k d) = _
    linarith
  rw [split]
  calc _ ≤ ∑ d ∈ Ioc 0 k, |tailTerm k d| := abs_sum_le_sum_abs _ _
       _ ≤ ∑ _d ∈ Ioc 0 k, (5/6:ℝ) := by
         apply sum_le_sum
         intro d hd
         obtain ⟨pos,cap⟩ := mem_Ioc.mp hd
         have dp : 0 < (d:ℝ) := Nat.cast_pos.mpr pos
         have dc : (d:ℝ) ≤ k := by exact_mod_cast cap
         have kp : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
         have arg : (10^8:ℝ) ≤ (k:ℝ)^2/d := large.trans ((le_div_iff₀ dp).mpr (by
           nlinarith [mul_le_mul_of_nonneg_left dc kp]))
         have mu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
         rw [tailTerm, abs_mul]
         exact (mul_le_of_le_one_left (abs_nonneg _) mu).trans (residual_five_sixths arg)
       _ = _ := by simp [mul_comm]

end
end RiemannReduction.DivisorBand.EarlySmall
