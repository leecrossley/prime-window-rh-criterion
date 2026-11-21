import CommonZeroTruncation
import CenteredRampDensity

open Finset MeasureTheory
open scoped Interval
namespace RiemannReduction.ZetaWindow
noncomputable section

private def kernel (z : ℂ) (u : ℝ) : ℂ :=
  ((analyticOrderNatAt riemannZeta z : ℂ)/z) * (u:ℂ)^(z-2)

private lemma kernel_eq {u : ℝ} (up : 0 < u) (z : ℂ) :
    kernel z u = zeroTerm z u / (u:ℂ)^2 := by
  simp only [kernel,zeroTerm,Complex.cpow_sub z 2 (Complex.ofReal_ne_zero.mpr up.ne'),
    Complex.cpow_ofNat]
  ring

private lemma kernel_integrable {a b : ℝ} (ap : 0 < a) (bp : 0 < b) (z : ℂ) :
    IntervalIntegrable (kernel z) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  have up := (lt_min ap bp).trans_le hu.1
  exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const u (z-2)
    (Or.inr up.ne'))).continuousWithinAt

private lemma kernel_bound {y a b : ℝ} (yp : 0 < y) (ya : y ≤ a) (ab : a ≤ b)
    {z : ℂ} (line : z.re = 1/2) :
    ‖∫ u in a..b, kernel z u‖ ≤ (2/Real.sqrt y)*(mass z/(‖z‖*‖z-1‖)) := by
  have ap := yp.trans_le ya
  have bp := ap.trans_le ab
  have off : z-2 ≠ -1 := by
    intro h
    have e := congrArg Complex.re h
    norm_num [line] at e
  have lap {u : ℝ} (hu : y ≤ u) : ‖(u:ℂ)^(z-1)‖ ≤ 1/Real.sqrt y := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (yp.trans_le hu),Complex.sub_re,Complex.one_re,line,
      show (1/2:ℝ)-1 = -(1/2) by norm_num,Real.rpow_neg (yp.le.trans hu),← Real.sqrt_eq_rpow,← one_div]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr yp) (Real.sqrt_le_sqrt hu)
  unfold kernel
  rw [intervalIntegral.integral_const_mul,integral_cpow (Or.inr ⟨off,Set.notMem_uIcc_of_lt ap bp⟩),
    show z-2+1=z-1 by ring,norm_mul,norm_div,norm_div,Complex.norm_natCast]
  have terms := (norm_sub_le ((b:ℂ)^(z-1)) ((a:ℂ)^(z-1))).trans
    (add_le_add (lap (ya.trans ab)) (lap ya))
  change mass z/‖z‖ * (_/‖z-1‖) ≤ _
  calc _ ≤ mass z/‖z‖ * ((1/Real.sqrt y+1/Real.sqrt y)/‖z-1‖) :=
           mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right terms (norm_nonneg _))
             (div_nonneg (mass_nonneg z) (norm_nonneg _))
       _ = _ := by ring

/-- After integrating, each zero contributes an extra inverse factor of z-1.
Under RH the resulting absolute sum is uniformly bounded at the square-root scale. -/
theorem smoothed_psi_on_rh (rh : RiemannHypothesis) : ∃ M > (0:ℝ),
    ∀ {y a b : ℝ}, 2 ≤ y → y ≤ a → a ≤ b → b ≤ 4*y →
      |∫ u in a..b, DivisorBand.density u| ≤ M/Real.sqrt y := by
  classical
  obtain ⟨B,Bp,trunc⟩ := common_zero_truncation
  obtain ⟨H,Hp,budget⟩ := finite_inverse_square_mass rh
  refine ⟨4*B+2*H,by positivity,fun {y a b} hy ya ab by4 => ?_⟩
  obtain ⟨S,hS,pointwise⟩ := trunc y hy
  have yp : 0 < y := by linarith
  have ap := yp.trans_le ya
  have bp := ap.trans_le ab
  let K (u : ℝ) := ∑ z ∈ S, kernel z u
  let F (u : ℝ) : ℂ := DivisorBand.density u
  have Fi : IntervalIntegrable F volume a b :=
    ⟨(DivisorBand.density_integrable ap bp).1.ofReal,(DivisorBand.density_integrable ap bp).2.ofReal⟩
  have Ki : IntervalIntegrable K volume a b :=
    ⟨integrable_finsetSum S (fun z _ => (kernel_integrable ap bp z).1),
     integrable_finsetSum S (fun z _ => (kernel_integrable ap bp z).2)⟩
  have point (u : ℝ) (hu : u ∈ Set.uIoc a b) : ‖F u+K u‖ ≤ B*Real.sqrt y/y^2 := by
    rw [Set.uIoc_of_le ab] at hu
    have yu := ya.trans hu.1.le
    have up := yp.trans_le yu
    have eq : F u+K u = ((psiError u:ℂ) + ∑ z ∈ S, zeroTerm z u)/(u:ℂ)^2 := by
      dsimp [F,K,DivisorBand.density,psiError]
      rw [Complex.ofReal_div,Complex.ofReal_pow,add_div,sum_div]
      simp only [kernel_eq up]
    rw [eq,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos up]
    exact div_le_div₀ (by positivity) (pointwise u yu (hu.2.trans by4))
      (sq_pos_of_pos yp) (pow_le_pow_left₀ yp.le yu 2)
  have error := intervalIntegral.norm_integral_le_of_norm_le_const point
  rw [abs_of_nonneg (sub_nonneg.mpr ab),intervalIntegral.integral_add Fi Ki] at error
  have err : ‖(∫ u in a..b, F u)+(∫ u in a..b, K u)‖ ≤ 4*B/Real.sqrt y := by
    apply error.trans
    calc (B*Real.sqrt y/y^2)*(b-a) ≤ (B*Real.sqrt y/y^2)*(4*y) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
         _ = 4*B/Real.sqrt y := by
            field_simp [yp.ne',(Real.sqrt_pos.mpr yp).ne']
            nlinarith [Real.sq_sqrt yp.le]
  have spectral : ‖∫ u in a..b, K u‖ ≤ (2/Real.sqrt y)*H := by
    dsimp [K]
    rw [intervalIntegral.integral_finsetSum (fun z _ => kernel_integrable ap bp z)]
    apply (norm_sum_le_of_le S (fun z hz => kernel_bound yp ya ab (re_of_rh rh (hS z hz)))).trans
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (budget S hS) (by positivity)
  have total := norm_sub_le ((∫ u in a..b, F u)+(∫ u in a..b, K u)) (∫ u in a..b, K u)
  rw [add_sub_cancel_right] at total
  have target : ‖∫ u in a..b, F u‖ = |∫ u in a..b, DivisorBand.density u| := by
    dsimp [F]
    rw [intervalIntegral.integral_ofReal,Complex.norm_real,Real.norm_eq_abs]
  rw [← target]
  exact total.trans ((add_le_add err spectral).trans_eq (by ring))

#print axioms smoothed_psi_on_rh
end
end RiemannReduction.ZetaWindow
