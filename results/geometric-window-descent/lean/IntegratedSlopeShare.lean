import Mathlib

/-! The integrated shortfall bound from twinheterodox's
    Three simplifications in the Alpöge–Claude argument for Dirichlet GRH,
    with the finite slope arrays and hypotheses of Formalism.HN.thmF_share. -/

open Finset MeasureTheory
open scoped Interval

namespace IntegratedSlopeShare

private theorem clipped_le_affine {z u h : ℝ} (hu : 0 ≤ u) (hh : 0 ≤ h)
    (pos : 0 < u+h) (hz : -u ≤ z) :
    min h (max z 0) ≤ h*(z+u)/(u+h) := by
  apply (le_div_iff₀ pos).mpr
  rcases le_total z 0 with zn | zp
  · rw [max_eq_right zn,min_eq_right hh,zero_mul]
    exact mul_nonneg hh (by linarith)
  rw [max_eq_left zp]
  rcases le_total z h with small | large
  · rw [min_eq_right small]
    nlinarith only [mul_le_mul_of_nonneg_right small hu]
  · rw [min_eq_left large]
    nlinarith only [mul_le_mul_of_nonneg_left large hh]

/-- The sharp integrated loss for the same finite input as the pointwise
    slope-fraction bound in the archived theorem. Multiplicities are explicit. -/
theorem integrated_share {I : Type} [Fintype I] (m : I → ℕ)
    (x : ∀ i, Fin (m i) → ℝ) (s u h : ℝ) (hu : 0 ≤ u) (hh : 0 ≤ h)
    (hsum : (∑ i, (m i : ℝ))*s ≤ ∑ i, ∑ j, x i j)
    (hle : ∀ i j, x i j ≤ s+u) :
    ∑ i, ∑ j, min h (max (s-x i j) 0) ≤ (∑ i, (m i : ℝ))*(u*h/(u+h)) := by
  classical
  by_cases pos : 0 < u+h
  · have cen : (∑ i, ∑ j : Fin (m i), ((s-x i j)+u)) ≤ (∑ i, (m i:ℝ))*u := by
      simp only [sum_add_distrib,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
        ←sum_mul]
      linarith
    calc _ ≤ ∑ i, ∑ j, h*((s-x i j)+u)/(u+h) := by
               apply sum_le_sum
               intro i _
               exact sum_le_sum (fun j _ => clipped_le_affine hu hh pos (by linarith [hle i j]))
         _ = (h/(u+h))*(∑ i, ∑ j, ((s-x i j)+u)) := by
               simp only [div_mul_eq_mul_div, ←Finset.sum_div, ←Finset.mul_sum]
         _ ≤ (h/(u+h))*((∑ i, (m i:ℝ))*u) :=
               mul_le_mul_of_nonneg_left cen (div_nonneg hh pos.le)
         _ = _ := by ring
  · have hz : h=0 := by linarith
    subst h
    simp

private theorem shortfall_integral (z h : ℝ) (hh : 0 ≤ h) :
    (∫ t in (0:ℝ)..h, if t<z then (1:ℝ) else 0) = min h (max z 0) := by
  have ind : (fun t : ℝ => if t<z then (1:ℝ) else 0) =
      (Set.Iio z).indicator (fun _ => (1:ℝ)) := by
    funext t
    simp [Set.indicator_apply]
  have inter : Set.Ioo (0:ℝ) h ∩ Set.Iio z = Set.Ioo 0 (min h z) := by
    ext t
    simp [and_assoc]
  rw [ind,intervalIntegral.integral_of_le hh,integral_Ioc_eq_integral_Ioo,
    setIntegral_indicator measurableSet_Iio,inter,setIntegral_const,smul_eq_mul,mul_one,
    MeasureTheory.measureReal_def,Real.volume_Ioo,sub_zero,ENNReal.toReal_ofReal']
  rcases le_total z 0 with zn|zp
  · rw [max_eq_right zn,min_eq_right hh,max_eq_right ((min_le_right h z).trans zn)]
  · rw [max_eq_left zp,max_eq_left (le_min hh zp)]

private theorem threshold_integrable (a s h : ℝ) :
    IntervalIntegrable (fun t : ℝ => if a<s-t then (1:ℝ) else 0) volume 0 h := by
  apply Antitone.intervalIntegrable
  intro v w vw
  by_cases hw : a<s-w
  · simp [hw,show a<s-v by linarith]
  · simp only [hw,if_false]
    split <;> norm_num

private theorem slope_shortfall_integral (a s h : ℝ) (hh : 0 ≤ h) :
    (∫ t in (0:ℝ)..h, if a<s-t then (1:ℝ) else 0) = min h (max (s-a) 0) := by
  have eqt (t : ℝ) : (a<s-t) = (t<s-a) := propext (by constructor <;> intro ht <;> linarith)
  simp_rw [eqt,shortfall_integral _ _ hh]

/-- Integrate the actual count of slopes below each threshold. A single
    shortfall contributes for exactly its truncated length. -/
theorem integral_threshold_count {I : Type} [Fintype I] (m : I → ℕ)
    (x : ∀ i, Fin (m i) → ℝ) (s u h : ℝ) (hu : 0 ≤ u) (hh : 0 ≤ h)
    (hsum : (∑ i, (m i : ℝ))*s ≤ ∑ i, ∑ j, x i j)
    (hle : ∀ i j, x i j ≤ s+u) :
    (∫ t in (0:ℝ)..h, ∑ i, ∑ j, if x i j < s-t then (1:ℝ) else 0) ≤
      (∑ i, (m i : ℝ))*(u*h/(u+h)) := by
  classical
  have row (i : I) : IntervalIntegrable
      (fun t : ℝ => ∑ j, if x i j<s-t then (1:ℝ) else 0) volume 0 h :=
    ⟨integrable_finsetSum _ (fun j _ => (threshold_integrable (x i j) s h).1),
     integrable_finsetSum _ (fun j _ => (threshold_integrable (x i j) s h).2)⟩
  rw [intervalIntegral.integral_finsetSum (fun i _ => row i)]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => threshold_integrable (x _ j) s h),
    slope_shortfall_integral _ _ _ hh]
  exact integrated_share m x s u h hu hh hsum hle

/-- Transfer the geometric rank inequality to the actual mean output slope.
    The input and target arrays are unnormalized to expose both ranks. -/
theorem rank_share_transfer {I J : Type} [Fintype I] [Fintype J] (m : I → ℕ)
    (x : ∀ i, Fin (m i) → ℝ) (y : J → ℝ) (s u h δ b : ℝ)
    (hu : 0 ≤ u) (hh : 0 ≤ h) (hd : δ < 1)
    (ni : 0 < ∑ i, (m i:ℝ)) (nj : 0 < (Fintype.card J:ℝ))
    (hsum : (∑ i, (m i : ℝ))*s ≤ ∑ i, ∑ j, x i j)
    (hle : ∀ i j, x i j ≤ s+u) (hy : ∀ j, s-h ≤ y j)
    (rank_bound : ∀ t ∈ Set.Icc (0:ℝ) h,
      ((1-δ)/(Fintype.card J:ℝ))*(∑ j, if y j<s-t then (1:ℝ) else 0) ≤
        b+(4/(∑ i, (m i:ℝ)))*(∑ i, ∑ j, if x i j<s-t then (1:ℝ) else 0)) :
    s - (∑ j, y j)/(Fintype.card J:ℝ) ≤
      (b*h+4*(u*h/(u+h)))/(1-δ) := by
  classical
  let f (t : ℝ) := ∑ j, if y j<s-t then (1:ℝ) else 0
  let g (t : ℝ) := ∑ i, ∑ j, if x i j<s-t then (1:ℝ) else 0
  have fi : IntervalIntegrable f volume 0 h :=
    ⟨integrable_finsetSum _ (fun j _ => (threshold_integrable (y j) s h).1),
     integrable_finsetSum _ (fun j _ => (threshold_integrable (y j) s h).2)⟩
  have row (i : I) : IntervalIntegrable
      (fun t : ℝ => ∑ j, if x i j<s-t then (1:ℝ) else 0) volume 0 h :=
    ⟨integrable_finsetSum _ (fun j _ => (threshold_integrable (x i j) s h).1),
     integrable_finsetSum _ (fun j _ => (threshold_integrable (x i j) s h).2)⟩
  have gi : IntervalIntegrable g volume 0 h :=
    ⟨integrable_finsetSum _ (fun i _ => (row i).1), integrable_finsetSum _ (fun i _ => (row i).2)⟩
  have output : (Fintype.card J:ℝ)*s - ∑ j, y j ≤ ∫ t in (0:ℝ)..h, f t := by
    dsimp [f]
    rw [intervalIntegral.integral_finsetSum (fun j _ => threshold_integrable (y j) s h)]
    have each (j : J) : s-y j ≤ ∫ t in (0:ℝ)..h, if y j<s-t then (1:ℝ) else 0 := by
      rw [slope_shortfall_integral _ _ _ hh]
      exact le_min (by linarith [hy j]) (le_max_left _ _)
    have total := sum_le_sum (s:=univ) (fun (j : J) _ => each j)
    simpa only [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul] using total
  have area : (∫ t in (0:ℝ)..h, g t) ≤ (∑ i, (m i:ℝ))*(u*h/(u+h)) :=
    integral_threshold_count m x s u h hu hh hsum hle
  have transferred := intervalIntegral.integral_mono_on hh
    (fi.const_mul ((1-δ)/(Fintype.card J:ℝ)))
    ((intervalIntegrable_const (c:=b)).add (gi.const_mul (4/(∑ i, (m i:ℝ))))) rank_bound
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add intervalIntegrable_const
    (gi.const_mul _),intervalIntegral.integral_const,intervalIntegral.integral_const_mul,
    smul_eq_mul,sub_zero] at transferred
  have hp : 0 < 1-δ := by linarith
  have left := mul_le_mul_of_nonneg_left output (div_nonneg hp.le nj.le)
  have right := mul_le_mul_of_nonneg_left area (div_nonneg (by norm_num : (0:ℝ)≤4) ni.le)
  apply (le_div_iff₀ hp).mpr
  calc _ = ((1-δ)/(Fintype.card J:ℝ))*((Fintype.card J:ℝ)*s-∑ j, y j) := by field_simp
       _ ≤ _ := left.trans transferred
       _ ≤ b*h+(4/(∑ i, (m i:ℝ)))*((∑ i, (m i:ℝ))*(u*h/(u+h))) := by linarith
       _ = _ := by field_simp [ni.ne']

/-- The two possible shortfalls h and −u, with weights u/(u+h) and h/(u+h),
    have mean zero and attain the claimed loss. -/
theorem sharp_two_slopes {u h : ℝ} (hu : 0 ≤ u) (hh : 0 ≤ h) (pos : 0 < u+h) :
    u/(u+h)+h/(u+h)=1 ∧ u/(u+h)*h + h/(u+h)*(-u)=0 ∧
    u/(u+h)*min h (max h 0)+h/(u+h)*min h (max (-u) 0) = u*h/(u+h) := by
  rw [max_eq_left hh,max_eq_right (neg_nonpos.mpr hu),min_self,min_eq_right hh]
  constructor
  · field_simp [pos.ne']
  constructor <;> ring

#print axioms integrated_share
#print axioms integral_threshold_count
#print axioms rank_share_transfer
#print axioms sharp_two_slopes

end IntegratedSlopeShare
