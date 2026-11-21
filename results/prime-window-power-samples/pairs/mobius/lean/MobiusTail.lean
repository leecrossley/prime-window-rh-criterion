import BandQuadrature

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace RiemannReduction.DivisorBand
noncomputable section

def mainSlope : ℝ := c*Real.eulerMascheroniConstant - logMoment

private theorem coefficient_bounds :
    1/4 ≤ c ∧ c ≤ 1/2 ∧ 0 ≤ mainSlope ∧ mainSlope ≤ 1 := by
  have l := Real.log_two_lt_d9
  have h := Real.log_two_gt_d9
  have g := Real.one_half_lt_eulerMascheroniConstant
  have G := Real.eulerMascheroniConstant_lt_two_thirds
  have lg : 0 ≤ Real.log 2 := by linarith
  have small : Real.log 2 ≤ 1 := by linarith
  have prod := mul_le_mul small (by linarith : Real.eulerMascheroniConstant ≤ 1)
    (by linarith : 0 ≤ Real.eulerMascheroniConstant) (by norm_num : (0:ℝ) ≤ 1)
  have square := mul_le_mul_of_nonneg_right small lg
  dsimp [mainSlope,c,logMoment]
  refine ⟨by linarith,by linarith,?_,?_⟩ <;>
    nlinarith [mul_nonneg lg (show 0 ≤ Real.eulerMascheroniConstant by linarith),sq_nonneg (Real.log 2)]

private lemma harmonic_floor_error {x : ℝ} (hx : 1 ≤ x) :
    |x*((harmonic ⌊x⌋₊:ℝ)-Real.log x-Real.eulerMascheroniConstant)| ≤ 2 := by
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
    exact (div_le_iff₀ np).mpr (by linarith))

/-- The divisor residual after removing the floor main term is uniformly bounded
at every real argument arising in Möbius inversion. -/
theorem residual_bounded {x : ℝ} (hx : 1 ≤ x) : |residual mainSlope x| ≤ 100 := by
  obtain ⟨cLo,cHi,aLo,aHi⟩ := coefficient_bounds
  have floorLow : (⌊x⌋₊:ℝ) ≤ x := Nat.floor_le (by linarith)
  have floorHigh := Nat.lt_floor_add_one x
  by_cases big : 16 ≤ x
  · have h := harmonic_floor_error hx
    have band := log_band_error big
    have split : residual mainSlope x =
        c*(x*((harmonic ⌊x⌋₊:ℝ)-Real.log x-Real.eulerMascheroniConstant)) -
        (dilate ArithmeticFunction.log window x-(c*x*Real.log x+logMoment*x)) +
        mainSlope*(x-⌊x⌋₊) := by unfold residual mainSlope; ring
    have hsmall : |c*(x*((harmonic ⌊x⌋₊:ℝ)-Real.log x-Real.eulerMascheroniConstant))| ≤ 1 := by
      rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ c)]
      nlinarith [mul_le_mul_of_nonneg_left h (show 0 ≤ c by linarith)]
    have af : 0 ≤ mainSlope*(x-⌊x⌋₊) := mul_nonneg aLo (sub_nonneg.mpr floorLow)
    have atMost : mainSlope*(x-⌊x⌋₊) ≤ 1 := (mul_le_of_le_one_right aLo (by linarith)).trans aHi
    rw [split]
    simp only [abs_le] at hsmall band ⊢
    constructor <;> linarith
  have log16 : Real.log 16 < 4 := by
    rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have lg : Real.log x ≤ 4 := (Real.log_le_log (by linarith) (le_of_not_ge big)).trans log16.le
  have H := harmonic_floor_le_one_add_log x hx
  have hp : (0:ℝ) ≤ harmonic ⌊x⌋₊ := (Real.log_nonneg hx).trans (log_le_harmonic_floor x (by linarith))
  have cx : 0 ≤ c*x := mul_nonneg (by linarith) (by linarith)
  have Hterm := mul_le_mul (mul_le_mul cHi (le_of_not_ge big) (by linarith) (by norm_num : (0:ℝ) ≤ 1/2))
    (show (harmonic ⌊x⌋₊:ℝ) ≤ 5 by linarith) hp (by norm_num : (0:ℝ) ≤ 1/2*16)
  have logPos : 0 ≤ dilate ArithmeticFunction.log window x := sum_nonneg (fun n _ =>
    mul_nonneg (Real.log_natCast_nonneg n) (ThetaTransfer.tent_nonneg _))
  have logCap : dilate ArithmeticFunction.log window x ≤ 64 := calc
    _ ≤ ∑ _n ∈ Icc 1 ⌊x⌋₊, (4:ℝ) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨np,lim⟩ := mem_Icc.mp hn
      have ln := (Real.log_le_log (Nat.cast_pos.mpr np) ((Nat.cast_le.mpr lim).trans floorLow)).trans lg
      exact (mul_le_of_le_one_right (Real.log_natCast_nonneg n) (ThetaTransfer.tent_le_one _)).trans ln
    _ = (⌊x⌋₊:ℝ)*4 := by simp
    _ ≤ _ := by linarith
  have af0 := mul_nonneg aLo (Nat.cast_nonneg (α := ℝ) ⌊x⌋₊)
  have af1 := mul_le_mul_of_nonneg_right aHi (Nat.cast_nonneg (α := ℝ) ⌊x⌋₊)
  unfold residual
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg cx hp]

/-- The actual signed summand at square scale. -/
def tailTerm (k d : ℕ) : ℝ := (ArithmeticFunction.moebius d:ℝ)*residual mainSlope ((k:ℝ)^2/d)

theorem tailTerm_abs_le {k d : ℕ} (pos : 0 < d) (cap : d ≤ k^2) : |tailTerm k d| ≤ 100 := by
  have dp : 0 < (d:ℝ) := Nat.cast_pos.mpr pos
  have arg : 1 ≤ (k:ℝ)^2/d := (le_div_iff₀ dp).mpr (by exact_mod_cast (by simpa using cap : 1*d ≤ k^2))
  have mu : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [tailTerm,abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) mu).trans (residual_bounded arg)

/-- The signed portion of the exact reconstruction above the hyperbola cutoff. -/
def largeDivisorSum (k : ℕ) : ℝ :=
  ∑ d ∈ Ioc k (k^2), tailTerm k d

/-- Taking absolute values for every divisor up to k costs at most 100k. -/
theorem small_divisors_cost {k : ℕ} (hk : 0 < k) :
    |PrimeGrid.powerMargin (k^2) - mainSlope - largeDivisorSum k| ≤ 100*k := by
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
       _ ≤ ∑ _d ∈ Ioc 0 k, (100:ℝ) := by
         apply sum_le_sum
         intro d hd
         obtain ⟨pos,cap⟩ := mem_Ioc.mp hd
         exact tailTerm_abs_le pos (cap.trans kk)
       _ = _ := by simp [mul_comm]

/-- The two signed estimates differ by an absolute allowance per root index. -/
theorem tail_margin_comparison {k : ℕ} (hk : 0 < k) :
    largeDivisorSum k - 100*k ≤ PrimeGrid.powerMargin (k^2) ∧
    PrimeGrid.powerMargin (k^2) - 101*k ≤ largeDivisorSum k := by
  obtain ⟨_,_,lo,hi⟩ := coefficient_bounds
  obtain ⟨lower,upper⟩ := abs_le.mp (small_divisors_cost hk)
  have k1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  constructor <;> linarith

#print axioms residual_bounded
#print axioms small_divisors_cost
#print axioms tail_margin_comparison
end
end RiemannReduction.DivisorBand
