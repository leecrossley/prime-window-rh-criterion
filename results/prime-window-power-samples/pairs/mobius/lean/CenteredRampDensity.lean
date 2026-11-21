import CenteredPrimeRamps

open Finset MeasureTheory
open scoped Interval ArithmeticFunction.vonMangoldt
namespace RiemannReduction.DivisorBand
noncomputable section

def density (u : ℝ) : ℝ := (Chebyshev.psi u-u)/u^2

private lemma psi_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u : ℝ => Chebyshev.psi u/u^2) volume a b := by
  simp only [div_eq_mul_inv]
  apply Chebyshev.psi_mono.intervalIntegrable.mul_continuousOn
  intro u hu
  have up := (lt_min ha hb).trans_le hu.1
  fun_prop (disch := positivity)

theorem density_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable density volume a b := by
  change IntervalIntegrable (fun u : ℝ => (Chebyshev.psi u-u)/u^2) volume a b
  simp only [div_eq_mul_inv]
  apply (Chebyshev.psi_mono.intervalIntegrable.sub
    (continuous_id.intervalIntegrable a b (μ:=volume))).mul_continuousOn
  intro u hu
  have up := (lt_min ha hb).trans_le hu.1
  fun_prop (disch := positivity)

private lemma sz_normalized {x : ℝ} (hx : 1 ≤ x) :
    Formalism.Sz x/x = ∫ t in (1:ℝ)..x, Chebyshev.psi t/t^2 := by
  have xp : 0 < x := by linarith
  have der : ∀ t ∈ Set.Icc (1:ℝ) x, DifferentiableAt ℝ (fun w : ℝ => w⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (by linarith [ht.1] : t ≠ 0)).differentiableAt
  have int : IntegrableOn (deriv (fun w : ℝ => w⁻¹)) (Set.Icc 1 x) := by
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro t ht
    have tp : 0 < t := by linarith [ht.1]
    fun_prop (disch := positivity)
  have ab := sum_mul_eq_sub_integral_mul₀ (c:=ArithmeticFunction.vonMangoldt)
    ArithmeticFunction.map_zero x der int
  simp_rw [deriv_inv,← Chebyshev.psi_eq_sum_Icc] at ab
  rw [← intervalIntegral.integral_of_le hx] at ab
  have neg : (∫ t in (1:ℝ)..x, -(t^2)⁻¹*Chebyshev.psi t) =
      -(∫ t in (1:ℝ)..x, Chebyshev.psi t/t^2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _; ring
  rw [neg,Icc_eq_cons_Ioc (Nat.zero_le _),sum_cons] at ab
  simp only [Nat.cast_zero,inv_zero,zero_mul,zero_add] at ab
  have algebra : Formalism.Sz x/x =
      (∑ n ∈ Ioc 0 ⌊x⌋₊, (n:ℝ)⁻¹*Λ n) - x⁻¹*Chebyshev.psi x := by
    unfold Formalism.Sz Chebyshev.psi
    rw [show Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ from Icc_add_one_left_eq_Ioc ..,
      sum_div,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    have np : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr (mem_Ioc.mp hn).1).ne'
    field_simp [np,xp.ne']
  linarith

private lemma centered_increment {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Formalism.Gz b/b - Formalism.Gz a/a = ∫ u in a..b, density u := by
  have ap : 0 < a := by linarith
  have bp := ap.trans_le hab
  have telescope := intervalIntegral.integral_add_adjacent_intervals
    (psi_integrable one_pos ap) (psi_integrable ap bp)
  rw [← sz_normalized ha,← sz_normalized (ha.trans hab)] at telescope
  have inv : IntervalIntegrable (fun u : ℝ => 1/u) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have pos := (lt_min ap bp).trans_le ht.1
    fun_prop (disch := positivity)
  have eq : (∫ u in a..b, density u) =
      ∫ u in a..b, (Chebyshev.psi u/u^2 - 1/u) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have pos := (lt_min ap bp).trans_le ht.1
    unfold density
    field_simp
  rw [eq,intervalIntegral.integral_sub (psi_integrable ap bp) inv,
    integral_one_div_of_pos ap bp,Real.log_div bp.ne' ap.ne']
  have gz {u : ℝ} (up : 0 < u) :
      Formalism.Gz u/u = Formalism.Sz u/u-Real.log u+(1+Real.eulerMascheroniConstant) := by
    unfold Formalism.Gz
    field_simp
  rw [gz bp,gz ap]
  linarith

theorem deficit_eq_centered_integrals {y : ℝ} (hy : 1 ≤ y) :
    D (4*y) = 2*y*(∫ u in y..2*y, density u) - 4*y*(∫ u in 2*y..4*y, density u) := by
  have yp : 0 < y := by linarith
  rw [deficit_eq_gz (by positivity),show 4*y/2=2*y by ring,show 4*y/4=y by ring,
    ← centered_increment hy (by linarith),← centered_increment (by linarith) (by linarith)]
  field_simp
  ring

#print axioms deficit_eq_centered_integrals
end
end RiemannReduction.DivisorBand
