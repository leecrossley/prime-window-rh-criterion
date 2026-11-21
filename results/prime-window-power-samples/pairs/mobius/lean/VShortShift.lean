import VStripEstimate
import CenteredRampDensity

open Finset Filter MeasureTheory
open scoped Interval
namespace RiemannReduction.DivisorBand
noncomputable section

private def antiderivative (x : ℝ) := ∫ u in (1:ℝ)..x, density u

private lemma increment {a b : ℝ} (ap : 0<a) (bp : 0<b) :
    antiderivative b-antiderivative a = ∫ u in a..b, density u := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (density_integrable one_pos ap) (density_integrable ap bp)
  dsimp [antiderivative]; linarith

private lemma normalized {x : ℝ} (hx : 4≤x) :
    D x/x = (3/2)*antiderivative (x/2)-(1/2)*antiderivative (x/4)-antiderivative x := by
  have xp : 0<x := by linarith
  have id := deficit_eq_centered_integrals (y:=x/4) (by linarith)
  rw [show 4*(x/4)=x by ring,show 2*(x/4)=x/2 by ring,
    ←increment (by positivity) (by positivity),←increment (by positivity) xp] at id
  rw [id]; field_simp; ring

/-- A bound on the centered prime count controls changes in the normalized actual margin. -/
theorem normalized_margin_shift {a C x y : ℝ} (ha : 0≤a) (ha2 : a≤2) (cp : 0<C)
    (psi : ∀ t : ℝ, 2≤t → |ZetaWindow.psiError t| ≤ C*t^a)
    (hx : 8≤x) (lo : x≤y) (hi : y≤2*x) :
    |D y/y-D x/x| ≤ 192*C*(y-x)*x^(a-2) := by
  have xp : 0<x := by linarith
  let W := 64*C*(x^a/x^2)
  have wp : 0 ≤ W := by dsimp [W]; positivity
  have point {u : ℝ} (low : x/4 ≤ u) (high : u ≤ 2*x) : |density u| ≤ W := by
    have up : 0<u := by linarith
    have factor : (2:ℝ)^a ≤ 4 := (Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2).trans_eq (by norm_num)
    have numer : u^a ≤ 4*x^a := by
      calc _ ≤ (2*x)^a := Real.rpow_le_rpow up.le high ha
           _ ≤ _ := by rw [Real.mul_rpow (by norm_num) xp.le]; exact mul_le_mul_of_nonneg_right factor (by positivity)
    have square := pow_le_pow_left₀ (by positivity : 0≤x/4) low 2
    change |ZetaWindow.psiError u/u^2| ≤ _
    rw [abs_div,abs_of_nonneg (sq_nonneg u)]
    calc _ ≤ (C*(4*x^a))/(x/4)^2 := div_le_div₀ (by positivity)
           ((psi u (by linarith)).trans (mul_le_mul_of_nonneg_left numer cp.le)) (by positivity) square
         _ = _ := by dsimp [W]; ring
  have dist (q : ℝ) (one : 1≤q) (four : q≤4) :
      |antiderivative (y/q)-antiderivative (x/q)| ≤ W*(y-x) := by
    have qp : 0<q := by linarith
    have order := (div_le_div_iff_of_pos_right qp).mpr lo
    have yn : 0<y := by linarith
    rw [increment (div_pos xp qp) (div_pos yn qp)]
    have est := intervalIntegral.norm_integral_le_of_norm_le_const (f:=density) (a:=x/q) (b:=y/q) (C:=W) (by
      intro u hu
      rw [Set.uIoc_of_le order] at hu
      rw [Real.norm_eq_abs]
      exact point ((div_le_div_of_nonneg_left xp.le qp four).trans hu.1.le) (hu.2.trans ((div_le_self yn.le one).trans hi)))
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr order),←sub_div] at est
    exact est.trans (mul_le_mul_of_nonneg_left (div_le_self (sub_nonneg.mpr lo) one) wp)
  have d1 := abs_le.mp (by simpa using dist 1 (by norm_num) (by norm_num))
  have d2 := abs_le.mp (dist 2 (by norm_num) (by norm_num))
  have d4 := abs_le.mp (dist 4 (by norm_num) (by norm_num))
  rw [normalized (by linarith),normalized (by linarith)]
  have cap : 192*C*(y-x)*x^(a-2) = 3*(W*(y-x)) := by
    rw [Real.rpow_sub xp,Real.rpow_two]; dsimp [W]; ring
  rw [cap,abs_le]
  constructor <;> linarith [d1.1,d1.2,d2.1,d2.2,d4.1,d4.2]

/-- The normalized margin changes by less than any fixed fraction of the peak scale. -/
theorem relative_short_shift {a α θ C ε : ℝ} (ha : 0≤a) (ha2 : a≤2) (cp : 0<C)
    (psi : ∀ t : ℝ, 2≤t → |ZetaWindow.psiError t| ≤ C*t^a)
    (sub : α≤1) (gap : α+a-2 < θ-1) (ep : 0<ε) :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y → y ≤ x+x^α →
      |D y/y-D x/x| ≤ ε*x^(θ-1) := by
  let g := (θ-1)-(α+a-2)
  have grow := (tendsto_rpow_atTop (show 0<g by dsimp [g]; linarith)).eventually_ge_atTop (192*C/ε)
  filter_upwards [eventually_ge_atTop (8:ℝ),grow] with x hx big
  intro y lo hi
  have xp : 0<x := by linarith
  have xp1 : 1≤x := by linarith
  have small : x^α ≤ x := (Real.rpow_le_rpow_of_exponent_le xp1 sub).trans_eq (Real.rpow_one x)
  apply (normalized_margin_shift ha ha2 cp psi hx lo (by linarith)).trans
  calc _ ≤ 192*C*x^α*x^(a-2) := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (Real.rpow_nonneg xp.le _)
       _ = (192*C)*x^(α+a-2) := by rw [mul_assoc,←Real.rpow_add xp]; congr 2; ring
       _ ≤ (x^g*ε)*x^(α+a-2) :=
           mul_le_mul_of_nonneg_right ((div_le_iff₀ ep).mp big) (Real.rpow_nonneg xp.le _)
       _ = _ := by
           rw [mul_right_comm (x^g) ε,←Real.rpow_add xp,mul_comm _ ε]
           congr 2; dsimp [g]; ring

/-- A positive excursion of height x^θ forces a whole forward interval. -/
theorem positive_after_peak {a α θ C : ℝ} (ha : 0≤a) (ha2 : a≤2) (cp : 0<C)
    (psi : ∀ t : ℝ, 2≤t → |ZetaWindow.psiError t| ≤ C*t^a)
    (sub : α≤1) (gap : α+a-2 < θ-1) :
    ∀ᶠ x : ℝ in atTop, x^θ < D x → ∀ y : ℝ, x ≤ y → y ≤ x+x^α → 0 < D y := by
  filter_upwards [eventually_gt_atTop (0:ℝ),relative_short_shift ha ha2 cp psi sub gap one_pos]
    with x xp estimate
  intro peak y lo hi
  have bound := (abs_le.mp (estimate y lo hi)).1
  have high : x^(θ-1) < D x/x := by
    rw [Real.rpow_sub xp,Real.rpow_one]; exact div_lt_div_of_pos_right peak xp
  exact (div_pos_iff_of_pos_right (xp.trans_le lo)).mp (by linarith)

/-- A negative excursion above the square-root scale beats any fixed square-root
allowance throughout the forward interval. -/
theorem negative_after_peak {a α θ C M : ℝ} (ha : 0≤a) (ha2 : a≤2) (cp : 0<C)
    (psi : ∀ t : ℝ, 2≤t → |ZetaWindow.psiError t| ≤ C*t^a)
    (sub : α≤1) (gap : α+a-2 < θ-1) (th : 1/2<θ) (mp : 0≤M) :
    ∀ᶠ x : ℝ in atTop, D x < -x^θ → ∀ y : ℝ, x ≤ y → y ≤ x+x^α →
      D y < -M*Real.sqrt y := by
  have grow := (tendsto_rpow_atTop (show 0<θ-1/2 by linarith)).eventually_ge_atTop (2*M)
  filter_upwards [eventually_gt_atTop (0:ℝ),grow,
    relative_short_shift ha ha2 cp psi sub gap (show 0<(1/2:ℝ) by norm_num)] with x xp big est
  intro peak y lo hi
  have yp := xp.trans_le lo
  have bound := (abs_le.mp (est y lo hi)).2
  have low : D x/x < -x^(θ-1) := by
    rw [Real.rpow_sub xp,Real.rpow_one,←neg_div]; exact div_lt_div_of_pos_right peak xp
  have root : 2*M ≤ x^(θ-1)*Real.sqrt x := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add xp,show θ-1+1/2=θ-1/2 by ring]
    exact big
  have yr : 2*M ≤ x^(θ-1)*Real.sqrt y :=
    root.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt lo) (Real.rpow_nonneg xp.le _))
  have loss : M/Real.sqrt y ≤ (1/2)*x^(θ-1) :=
    (div_le_iff₀ (Real.sqrt_pos.mpr yp)).mpr (by linarith)
  have neg : D y/y < -(M/Real.sqrt y) := by linarith
  have id : -(M/Real.sqrt y)*y = -M*Real.sqrt y := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr yp)]
    nlinarith [Real.sq_sqrt yp.le]
  exact ((div_lt_iff₀ yp).mp neg).trans_eq id

#print axioms normalized_margin_shift
#print axioms positive_after_peak
#print axioms negative_after_peak
end
end RiemannReduction.DivisorBand
