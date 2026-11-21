import CutoffVariation
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open Finset
namespace RiemannReduction.BalancedCutoffs
noncomputable section

/-- Correct positive node weights simultaneously on a whole real space of sample vectors. -/
theorem positive_reweight {ι : Type*} [Fintype ι] (U : Submodule ℝ (ι → ℝ))
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) {t : ℝ} (ht : 0 ≤ t) (small : t < 1)
    (defect : ∀ x : U, |∑ i, p i * (x : ι → ℝ) i| ≤ ∑ i, (t*p i)*|(x : ι → ℝ) i|) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i ∧ |w i-p i| ≤ t*p i) ∧
      ∀ x : U, ∑ i, w i * (x : ι → ℝ) i = 0 := by
  classical
  let L : U →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ i, p i * (x : ι → ℝ) i
      map_add' := by intro x y; simp [mul_add, sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        apply sum_congr rfl
        intro i _
        ring }
  let N (x : ι → ℝ) := ∑ i, (t*p i)*|x i|
  have hom (c : ℝ) (hc : 0 < c) (x : ι → ℝ) : N (c • x) = c * N x := by
    simp only [N, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc, mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  have subadd (x y : ι → ℝ) : N (x+y) ≤ N x + N y := by
    simp only [N, Pi.add_apply, ← sum_add_distrib]
    apply sum_le_sum
    intro i _
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (mul_nonneg ht (hp i).le)
  obtain ⟨g, hext, bound⟩ := exists_extension_of_le_sublinear ⟨U,L⟩ N hom subadd
    (fun x => (le_abs_self _).trans (defect x))
  let e (i j : ι) : ℝ := if j = i then 1 else 0
  have coord (i : ι) : N (e i) = t*p i := by simp [N, e, apply_ite abs, mul_ite]
  have corr (i : ι) : |g (e i)| ≤ t*p i := by
    have a := bound (e i)
    have b := bound (-(e i))
    rw [coord] at a
    have even : N (-(e i)) = N (e i) := by simp [N]
    rw [map_neg, even, coord] at b
    exact abs_le.mpr ⟨by linarith,a⟩
  have expand (x : ι → ℝ) : ∑ i, g (e i) * x i = g x := by
    have decomp : ∑ i, x i • e i = x := by
      ext j
      simp [Finset.sum_apply, e, Pi.smul_apply, smul_eq_mul, mul_ite]
    calc
      ∑ i, g (e i) * x i = ∑ i, g (x i • e i) := by simp [mul_comm]
      _ = g x := by rw [← map_sum, decomp]
  refine ⟨fun i => p i - g (e i), ?_, ?_⟩
  · intro i
    have strict : t*p i < p i := by simpa using mul_lt_mul_of_pos_right small (hp i)
    have up := (abs_le.mp (corr i)).2
    exact ⟨by linarith, by simpa [sub_sub_cancel_left] using corr i⟩
  · intro x
    simp only [sub_mul, sum_sub_distrib, expand]
    exact sub_eq_zero.mpr (hext x).symm

/-- Complex power averaged over the actual arithmetic progression at a cutoff. -/
def arithmeticMode {ι : Type*} (a : ℕ) (b h r : ι → ℕ) (z : ℂ) (i : ι) : ℂ :=
  let I := (Finset.Icc a (b i)).filter (fun n => n % h i = r i)
  (I.card : ℂ)⁻¹ * ∑ n ∈ I, (n : ℂ)^z

/-- The relative defect on the real sample space gives one probability for all complex modes.
The index type can be the full grid or the grid inside a prescribed local interval. -/
theorem arithmetic_prefix_probabilities {ι : Type*} [Fintype ι] [Nonempty ι] (a : ℕ)
    (b h r : ι → ℕ) (Z : Set ℂ) (U : Submodule ℝ (ι → ℝ))
    (realMem : ∀ z ∈ Z, (fun i => (arithmeticMode a b h r z i).re) ∈ U)
    (imagMem : ∀ z ∈ Z, (fun i => (arithmeticMode a b h r z i).im) ∈ U)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) {t : ℝ} (ht : 0 ≤ t) (small : t < 1)
    (defect : ∀ x : U, |∑ i, p i * (x : ι → ℝ) i| ≤ ∑ i, (t*p i)*|(x : ι → ℝ) i|) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      ∀ z ∈ Z, ∑ i, (w i : ℂ) * arithmeticMode a b h r z i = 0 := by
  classical
  obtain ⟨w, bounds, vanishes⟩ := positive_reweight U p hp ht small defect
  let mass := ∑ i, w i
  have pos : 0 < mass := Finset.sum_pos (fun i _ => (bounds i).1) Finset.univ_nonempty
  have balanced (v : U) : ∑ i, (w i/mass)*(v : ι → ℝ) i = 0 := by
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, vanishes, zero_div]
  refine ⟨fun i => w i/mass, fun i => div_pos (bounds i).1 pos, ?_, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self pos.ne'
  · intro z hz
    apply Complex.ext
    · simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.zero_re]
      exact balanced ⟨_, realMem z hz⟩
    · simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, Complex.zero_im]
      exact balanced ⟨_, imagMem z hz⟩

/-- A signed mass error expressed in terms of the continuous norm also bounds the grid defect. -/
theorem relative_defect {Z S e d : ℝ} (he : 0 ≤ e) (hsmall : e < 1)
    (signed : |d| ≤ e*Z) (norm : (1-e)*Z ≤ S) :
    |d| ≤ (e/(1-e))*S := by
  have pos := sub_pos.mpr hsmall
  have step := mul_le_mul_of_nonneg_left norm (div_nonneg he pos.le)
  calc
    |d| ≤ e*Z := signed
    _ = (e/(1-e))*((1-e)*Z) := by field_simp
    _ ≤ _ := step

theorem gain_loss {ι : Type*} [Fintype ι] (w v : ι → ℝ) (bal : ∑ i, w i*v i = 0) :
    ∑ i, w i*|v i| = 2 * ∑ i, w i*max (-(v i)) 0 := by
  have parts (i : ι) : w i*|v i| = w i*v i + 2*(w i*max (-(v i)) 0) := by
    by_cases h : 0 ≤ v i
    · rw [abs_of_nonneg h,max_eq_right (neg_nonpos.mpr h)]; ring
    · rw [abs_of_neg (lt_of_not_ge h),max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]; ring
  simp only [parts, sum_add_distrib, ← mul_sum, bal, zero_add]

/-- Recover the raw summand from its log-variable primitive on a real prefix. -/
theorem log_prefix_derivative {P : ℝ → ℝ} {x d : ℝ} (hx : 0 < x)
    (hp : HasDerivAt P d (Real.log x)) :
    HasDerivAt (fun t : ℝ => t*P (Real.log t)) (P (Real.log x)+d) x := by
  apply ((hasDerivAt_id x).mul (hp.comp x (Real.hasDerivAt_log hx.ne'))).congr_deriv
  change 1 * P (Real.log x) + x * (d * x⁻¹) = P (Real.log x) + d
  field_simp [hx.ne']

end
end RiemannReduction.BalancedCutoffs
