import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Finset MeasureTheory Set
open scoped Interval

namespace RiemannReduction.CutoffVariation
noncomputable section

/-- Integrating an exact finite shift identity bounds the variation by local L¹ mass. -/
theorem shift_integral {ι : Type*} (S : Finset ι) (c d : ι → ℝ)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) {a b : ℝ} (ab : a ≤ b)
    (short : ∀ i ∈ S, |d i| ≤ 1)
    (identity : ∀ x ∈ Icc a b, g x = ∑ i ∈ S, c i * f (x + d i)) :
    (∫ x in a..b, |g x|) ≤ (∑ i ∈ S, |c i|) * ∫ x in a-1..b+1, |f x| := by
  have hi (i : ι) : Continuous (fun x : ℝ => |c i| * |f (x+d i)|) :=
    continuous_const.mul (hf.comp (continuous_id.add continuous_const)).abs
  calc
    (∫ x in a..b, |g x|) ≤ ∫ x in a..b, ∑ i ∈ S, |c i| * |f (x+d i)| := by
      apply intervalIntegral.integral_mono_on ab (hg.abs.intervalIntegrable _ _)
        ((continuous_finsetSum S (fun i _ => hi i)).intervalIntegrable _ _)
      intro x hx
      rw [identity x hx]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun i => c i*f (x+d i)) S
    _ = ∑ i ∈ S, |c i| * ∫ x in a+d i..b+d i, |f x| := by
      rw [intervalIntegral.integral_finsetSum (fun i _ => (hi i).intervalIntegrable _ _)]
      apply sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right (f := fun x => |f x|)]
    _ ≤ _ := by
      rw [sum_mul]
      apply sum_le_sum
      intro i mem
      obtain ⟨lo, up⟩ := abs_le.mp (short i mem)
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall fun x => abs_nonneg (f x)) (hf.abs.intervalIntegrable _ _)

/-- Raising the clipping threshold costs at most the threshold times the interval length. -/
theorem threshold_integral (f : ℝ → ℝ) (hf : Continuous f)
    {a b t : ℝ} (ab : a ≤ b) (ht : 0 ≤ t) :
    (∫ x in a..b, max (f x) 0) - (b-a)*t ≤ ∫ x in a..b, max (f x-t) 0 := by
  have p : Continuous (fun x => max (f x) 0) := hf.max continuous_const
  have q : Continuous (fun x => max (f x-t) 0) := (hf.sub continuous_const).max continuous_const
  have point (x : ℝ) : max (f x) 0 ≤ max (f x-t) 0 + t :=
    max_le (by linarith [le_max_left (f x-t) 0]) (add_nonneg (le_max_right _ _) ht)
  have h := intervalIntegral.integral_mono_on ab (p.intervalIntegrable (μ := volume) _ _)
    ((q.add continuous_const).intervalIntegrable _ _) (fun x _ => point x)
  change (∫ x in a..b, max (f x) 0) ≤ ∫ x in a..b, max (f x-t) 0 + t at h
  rw [intervalIntegral.integral_add (q.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const] at h
  simp only [smul_eq_mul] at h
  linarith

/-- The mass and the variation give the reciprocal-frequency sign interval. -/
theorem component_width {W H K len : ℝ} (hW : 0 < W) (hH : 0 < H) (hK : 0 < K)
    (area : W/4 ≤ len * (384*H*(K*W))) : 1/(1536*H*K) ≤ len := by
  apply (div_le_iff₀ (by positivity : 0 < 1536*H*K)).mpr
  apply (mul_le_mul_iff_right₀ hW).mp
  nlinarith only [area]

end
end RiemannReduction.CutoffVariation
