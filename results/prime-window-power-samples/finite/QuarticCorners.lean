import Mathlib.Tactic

namespace QuarticCorners

noncomputable def hinge (t : ℝ) : ℝ := max t 0

noncomputable def tent (x p : ℝ) : ℝ :=
  if x ≤ p then 0 else if x ≤ 2*p then x/p - 1
  else if x ≤ 4*p then 2 - x/(2*p) else 0

/-- The three changes of slope for a single prime weight, including endpoints. -/
theorem tent_hinges (x p : ℝ) (hp : 0 < p) :
    tent x p = hinge (x-p)/p - 3*hinge (x-2*p)/(2*p) + hinge (x-4*p)/(2*p) := by
  unfold tent hinge
  simp only [max_def]
  split_ifs <;> first | linarith | (field_simp; ring)

/-- The exact remaining hinge change after subtracting the initial slope. -/
theorem hinge_remainder (x h a : ℝ) :
    hinge (x+h-a) - hinge (x-a) - (if a < x then h else 0) =
      if a < x then hinge (a-x-h) else hinge (x+h-a) := by
  unfold hinge
  simp only [max_def]
  split_ifs <;> linarith

/-- Averaging a mean-zero displacement makes each individual hinge gap nonnegative. -/
theorem mean_hinge_gap (s : Finset ℕ) (w h : ℕ → ℝ) (x a : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (centered : ∑ i ∈ s, w i*h i = 0) :
    0 ≤ ∑ i ∈ s, w i*(hinge (x+h i-a)-hinge (x-a)) := by
  have bound (i : ℕ) : (if a < x then h i else 0) ≤ hinge (x+h i-a)-hinge (x-a) := by
    apply sub_nonneg.mp
    rw [hinge_remainder]
    split <;> exact le_max_right _ _
  have summed := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (bound i) (hw i hi))
  by_cases order : a < x
  · simpa [order, centered] using summed
  · simpa [order] using summed

/-- The positive endpoint gaps can be dropped when bounding the loss. -/
theorem middle_corner (p A B C : ℝ) (hp : 0 < p) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    -(A/p - 3*B/(2*p) + C/(2*p)) ≤ 3*B/(2*p) := by
  have first := div_nonneg hA hp.le
  have last := div_nonneg hC (show 0 ≤ 2*p by positivity)
  linarith

end QuarticCorners
