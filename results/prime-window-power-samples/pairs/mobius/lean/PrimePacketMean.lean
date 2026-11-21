import WholeTailPNT
import LargePrimePackets

open Filter MeasureTheory Set Finset
open scoped Interval Topology ArithmeticFunction.zeta
namespace RiemannReduction.DivisorBand
noncomputable section

/-- At integer sample points the same centered function as in the prime groups
has a bounded total, even before averaging. -/
theorem all_integer_group_sum {x : ℝ} (hx : 1 ≤ x) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (D (x/n)-mainSlope)| ≤ 100 := by
  have bound := residual_bounded hx
  rw [divisor_residual_eq,dilate] at bound
  have eq : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.zeta n:ℝ)*D (x/n)) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, D (x/n) := by
    apply sum_congr rfl
    intro n hn
    simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt (mem_Icc.mp hn).1)]
  simp only [ArithmeticFunction.natCoe_apply] at bound
  rw [eq] at bound
  simpa [sum_sub_distrib,mul_comm] using bound

/-- Difference between sampling at primes above k and sampling all integers
with constant weight w. Here x=k² and the sampled function is D(x/n)-A. -/
def samplingError (k : ℕ) (w : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (k^2), ((if n.Prime ∧ k<n then 1 else 0)-w)*
    (D ((k:ℝ)^2/n)-mainSlope)

theorem prime_sampling_comparison {k : ℕ} (hk : 0 < k) (w : ℝ) :
    |D ((k:ℝ)^2) - (mainSlope + smoothSum k mainSlope - samplingError k w)| ≤ 100*|w| := by
  let x := (k:ℝ)^2
  have x1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ k^2 from Nat.pow_pos hk)
  have floor : ⌊x⌋₊ = k^2 := by dsimp [x]; rw [← Nat.cast_pow,Nat.floor_natCast]
  have bound := all_integer_group_sum x1
  rw [floor] at bound
  have decomp := large_prime_partition hk mainSlope
  let f (n : ℕ) := D (x/n)-mainSlope
  have centered : samplingError k w = (∑ p ∈ primesAboveRoot k, f p) -
      w*∑ n ∈ Finset.Icc 1 (k^2), f n := by
    dsimp [samplingError,primesAboveRoot]
    rw [sum_filter,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    dsimp [f,x]
    split_ifs <;> ring
  change D x=mainSlope+smoothSum k mainSlope-∑ p ∈ primesAboveRoot k, f p at decomp
  have eq : D x - (mainSlope + smoothSum k mainSlope - samplingError k w) =
      -(w*∑ n ∈ Finset.Icc 1 (k^2), f n) := by rw [centered,decomp]; ring
  change |D x - _| ≤ _
  rw [eq,abs_neg,abs_mul,mul_comm (100:ℝ)]
  exact mul_le_mul_of_nonneg_left bound (abs_nonneg _)

private def F (t : ℝ) := Formalism.Gz t/t^2
private def I (x : ℝ) := ∫ t in (1:ℝ)..x, F t
private def J (x : ℝ) := ∫ t in x/2..x, F t

private lemma G_continuous {t : ℝ} (tp : 0 < t) : ContinuousAt Formalism.Gz t := by
  have s : ContinuousAt Formalism.Sz t := Complex.continuous_re.continuousAt.comp
    (Formalism.ZF.perron_Sz_continuousAt t)
  change ContinuousAt (fun u : ℝ => Formalism.Sz u-u*Real.log u+(1+Real.eulerMascheroniConstant)*u) t
  fun_prop (disch := positivity)

private lemma F_continuous {t : ℝ} (tp : 0 < t) : ContinuousAt F t :=
  (G_continuous tp).div (continuousAt_id.pow 2) (pow_ne_zero _ tp.ne')

private lemma F_int {a b : ℝ} (ap : 0 < a) (bp : 0 < b) : IntervalIntegrable F volume a b :=
  (continuousOn_of_forall_continuousAt fun _ ht => F_continuous ((lt_min ap bp).trans_le ht.1)).intervalIntegrable

private lemma difference {a b : ℝ} (ap : 0 < a) (bp : 0 < b) :
    (∫ t in a..b, F t) = I b-I a := by
  have h := intervalIntegral.integral_add_adjacent_intervals (F_int one_pos ap) (F_int ap bp)
  unfold I
  linarith

private lemma small {x : ℝ} (xp : 0 < x) (cap : x ≤ 1) :
    I x = (1+Real.eulerMascheroniConstant)*Real.log x-(Real.log x)^2/2 := by
  let P (t : ℝ) := (1+Real.eulerMascheroniConstant)*Real.log t-(Real.log t)^2/2
  have der (t : ℝ) (ht : t ∈ [[1,x]]) : HasDerivAt P (F t) t := by
    rw [Set.uIcc_comm,Set.uIcc_of_le cap] at ht
    have tp := xp.trans_le ht.1
    have d := Real.hasDerivAt_log tp.ne'
    apply ((d.const_mul (1+Real.eulerMascheroniConstant)).sub ((d.pow 2).div_const 2)).congr_deriv
    rw [F,Formalism.Gz,Formalism.ZF.perron_Sz_eq_zero_of_le_one ht.2]
    field_simp
    ring
  rw [I,intervalIntegral.integral_eq_sub_of_hasDerivAt der (F_int one_pos xp)]
  simp [P]

private lemma boundary : -(3/2)*I (1/2) + (1/2)*I (1/4) = mainSlope := by
  rw [small (by norm_num) (by norm_num),small (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num),Real.log_div (by norm_num) (by norm_num),
    show (4:ℝ)=2^2 by norm_num,Real.log_pow]
  simp only [Real.log_one,Nat.cast_ofNat]
  unfold mainSlope c logMoment
  ring

private lemma endpoint_formula {x : ℝ} (xp : 0 < x) :
    (∫ t in (1:ℝ)..x, D t/t^2) = mainSlope + J (x/2)/2 - J x := by
  have pos (t : ℝ) (ht : t ∈ [[1,x]]) := (lt_min (by norm_num : (0:ℝ)<1) xp).trans_le ht.1
  have scaled (c : ℝ) (cp : 0 < c) : IntervalIntegrable (fun t : ℝ => F (t/c)) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    exact (F_continuous (div_pos (pos t ht) cp)).comp (f:=fun u : ℝ => u/c) (continuousAt_id.div_const c)
  have eq : (∫ t in (1:ℝ)..x, D t/t^2) =
      ∫ t in (1:ℝ)..x, -F t+(3/4)*F (t/2)-(1/8)*F (t/4) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change D t/t^2 = -F t+(3/4)*F (t/2)-(1/8)*F (t/4)
    rw [deficit_eq_gz (pos t ht)]
    dsimp [F]
    ring
  have neg : IntervalIntegrable (fun t => -F t) volume 1 x := (F_int one_pos xp).neg
  have two : IntervalIntegrable (fun t => (3/4)*F (t/2)) volume 1 x :=
    (scaled 2 (by norm_num)).const_mul _
  have four : IntervalIntegrable (fun t => (1/8)*F (t/4)) volume 1 x :=
    (scaled 4 (by norm_num)).const_mul _
  have add : IntervalIntegrable (fun t => -F t+(3/4)*F (t/2)) volume 1 x := neg.add two
  rw [eq,intervalIntegral.integral_sub add four,intervalIntegral.integral_add neg two,
    intervalIntegral.integral_neg,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_div F (by norm_num : (2:ℝ) ≠ 0),
    intervalIntegral.integral_comp_div F (by norm_num : (4:ℝ) ≠ 0)]
  change -I x + (3/4)*(2*(∫ t in 1/2..x/2, F t)) - (1/8)*(4*(∫ t in 1/4..x/4, F t)) =
      mainSlope+J (x/2)/2-J x
  rw [difference (by norm_num) (by positivity),difference (by norm_num) (by positivity),
    J,J,difference (by positivity) (by positivity),difference (by positivity) xp,
    show x/2/2=x/4 by ring,← boundary]
  ring

private lemma J_zero : Tendsto J atTop (𝓝 0) := by
  obtain ⟨c,A,cp,pnt⟩ := Formalism.ZF.gzPNT
  have growth : Tendsto (fun x : ℝ => x/2) atTop atTop := by
    simpa [div_eq_mul_inv] using (tendsto_id (α:=ℝ) (x:=atTop)).atTop_mul_const (by norm_num : (0:ℝ)<2⁻¹)
  have decay := Real.tendsto_exp_atBot.comp ((Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp growth)).const_mul_atTop_of_neg (neg_neg_of_pos cp))
  have zero : Tendsto (fun x : ℝ => |A| * Real.exp (-c*Real.sqrt (Real.log (x/2)))) atTop (𝓝 0) :=
    by simpa only [mul_zero,Function.comp_apply] using (tendsto_const_nhds (x:=|A|)).mul decay
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ zero
  filter_upwards [eventually_ge_atTop (4:ℝ)] with x hx
  let E := Real.exp (-c*Real.sqrt (Real.log (x/2)))
  have xp : 0 < x/2 := by linarith
  have bound (t : ℝ) (ht : t ∈ uIoc (x/2) x) : ‖F t‖ ≤ |A| * E/(x/2) := by
    rw [uIoc_of_le (by linarith)] at ht
    have tp := xp.trans ht.1
    have h := pnt t (by linarith [ht.1])
    have le : Real.exp (-c*Real.sqrt (Real.log t)) ≤ E := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt (Real.log_le_log xp ht.1.le)) (neg_nonpos.mpr cp.le)
    have narrow : |Formalism.Gz t| ≤ |A| * t * E := h.trans
      (mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self A) tp.le) le
        (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) tp.le))
    rw [Real.norm_eq_abs,F,abs_div,abs_of_nonneg (sq_nonneg t)]
    calc _ ≤ (|A| * t * E)/t^2 := div_le_div_of_nonneg_right narrow (sq_nonneg _)
         _ = (|A| * E)/t := by field_simp
         _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) xp ht.1.le
  have est := intervalIntegral.norm_integral_le_of_norm_le_const bound
  rw [show x-x/2=x/2 by ring,abs_of_pos xp,div_mul_cancel₀ _ xp.ne'] at est
  exact est

/-- Exact zero signed mean of the function sampled by the prime groups. -/
theorem prime_group_profile_mean_zero :
    Tendsto (fun x : ℝ => ∫ t in (1:ℝ)..x, (D t-mainSlope)/t^2) atTop (𝓝 0) := by
  have growth : Tendsto (fun x : ℝ => x/2) atTop atTop := by
    simpa [div_eq_mul_inv] using (tendsto_id (α:=ℝ) (x:=atTop)).atTop_mul_const (by norm_num : (0:ℝ)<2⁻¹)
  have frac : Tendsto (fun x : ℝ => mainSlope/x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have limit := (frac.add ((J_zero.comp growth).div_const 2)).sub J_zero
  simp only [zero_div,add_zero,sub_zero] at limit
  apply limit.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have xp : 0 < x := by linarith
  have pos (t : ℝ) (ht : t ∈ [[1,x]]) := (lt_min (by norm_num : (0:ℝ)<1) xp).trans_le ht.1
  have di : IntervalIntegrable (fun t => D t/t^2) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    have heq : EqOn (fun t => D t/t^2) (fun t =>
        (-Formalism.Gz t+3*Formalism.Gz (t/2)-2*Formalism.Gz (t/4))/t^2) [[1,x]] :=
      fun t ht => congrArg (· / t^2) (deficit_eq_gz (pos t ht))
    apply ContinuousOn.congr _ heq
    intro t ht
    have tp := pos t ht
    have u := G_continuous tp
    have v := (G_continuous (by positivity : 0 < t/2)).comp (f:=fun s : ℝ => s/2) (continuousAt_id.div_const 2)
    have w := (G_continuous (by positivity : 0 < t/4)).comp (f:=fun s : ℝ => s/4) (continuousAt_id.div_const 4)
    exact (((u.neg.add (v.const_mul 3)).sub (w.const_mul 2)).div (continuousAt_id.pow 2)
      (pow_ne_zero _ tp.ne')).continuousWithinAt
  have ai : IntervalIntegrable (fun t : ℝ => mainSlope/t^2) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have tp := pos t ht
    fun_prop (disch := positivity)
  have ant : (∫ t in (1:ℝ)..x, mainSlope/t^2) = mainSlope-mainSlope/x := by
    have deriv (t : ℝ) (ht : t ∈ [[1,x]]) :
        HasDerivAt (fun u : ℝ => -mainSlope*u⁻¹) (mainSlope/t^2) t := by
      apply ((hasDerivAt_inv (pos t ht).ne').const_mul (-mainSlope)).congr_deriv
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt deriv ai]
    simp; ring
  simp_rw [sub_div]
  rw [intervalIntegral.integral_sub di ai,ant,endpoint_formula xp]
  dsimp [Function.comp_def]
  ring

#print axioms all_integer_group_sum
#print axioms prime_sampling_comparison
#print axioms prime_group_profile_mean_zero
end
end RiemannReduction.DivisorBand
