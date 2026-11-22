import IntegratedSlopeShare

open Finset
namespace FiniteSlopeShare
noncomputable section

/-- Length of the part of [a,b] lying below z. -/
def width (a b z : ℝ) : ℝ := min b (max a z)-a

private theorem width_split {a c b : ℝ} (ac : a ≤ c) (cb : c ≤ b) (z : ℝ) :
    width a b z = width a c z + width c b z := by
  unfold width
  rcases le_total z a with za | az
  · rw [max_eq_left za,max_eq_left (za.trans ac),min_eq_right (ac.trans cb),min_eq_right ac,min_eq_right cb]
    ring
  rw [max_eq_right az]
  rcases le_total z c with zc | cz
  · rw [max_eq_left zc,min_eq_right (zc.trans cb),min_eq_right zc,min_eq_right cb]
    ring
  · rw [max_eq_right cz,min_eq_left cz]
    ring

/-- Summing the lengths of the finitely many intervals between thresholds
    transfers a bound on signed threshold counts to one on clipped shortfalls. -/
theorem finite_threshold_bound {A : Type*} (samples : Finset A)
    (value weight : A → ℝ) (ceiling : ℝ) {a b : ℝ} (ab : a ≤ b)
    (bound : ∀ t ∈ Set.Ico a b, (∑ i ∈ samples, weight i*(if t<value i then 1 else 0)) ≤ ceiling) :
    (∑ i ∈ samples, weight i*width a b (value i)) ≤ ceiling*(b-a) := by
  classical
  have subdivide (cuts : Finset ℝ) {a b : ℝ} (ab : a ≤ b)
      (covers : ∀ i ∈ samples, a<value i → value i<b → value i∈cuts)
      (bound : ∀ t ∈ Set.Ico a b, (∑ i ∈ samples, weight i*(if t<value i then 1 else 0)) ≤ ceiling) :
      (∑ i ∈ samples, weight i*width a b (value i)) ≤ ceiling*(b-a) := by
    induction cuts using Finset.induction_on generalizing a b with
    | empty =>
      rcases eq_or_lt_of_le ab with eq | lt
      · subst b
        simp [width]
      · have cell (i : A) (mem : i∈samples) :
            width a b (value i) = (if a<value i then (1:ℝ) else 0)*(b-a) := by
          by_cases high : a<value i
          · have top : b ≤ value i := by
              by_contra! below
              exact Finset.notMem_empty _ (covers i mem high below)
            simp [width,high,max_eq_right high.le,min_eq_left top]
          · have lo := le_of_not_gt high
            simp [width,high,max_eq_left lo,min_eq_right ab]
        calc (∑ i ∈ samples, weight i*width a b (value i))
             = (∑ i ∈ samples, weight i*(if a<value i then 1 else 0))*(b-a) := by
                  rw [Finset.sum_mul]
                  exact Finset.sum_congr rfl (fun i hi => by rw [cell i hi]; ring)
             _ ≤ _ := mul_le_mul_of_nonneg_right (bound a ⟨le_rfl,lt⟩) (sub_nonneg.mpr ab)
    | @insert v cuts _ ih =>
      let c := min b (max a v)
      have ac : a ≤ c := le_min ab (le_max_left _ _)
      have cb : c ≤ b := min_le_left _ _
      have left := ih ac (fun i hi lower upper => by
        have mem := covers i hi lower (upper.trans_le cb)
        apply (mem_insert.mp mem).resolve_left
        intro eqv
        rw [eqv] at lower upper
        have cv : c ≤ v := (min_le_right b (max a v)).trans_eq (max_eq_right lower.le)
        exact (not_lt_of_ge cv) upper)
        (fun t ht => bound t ⟨ht.1,ht.2.trans_le cb⟩)
      have right := ih cb (fun i hi lower upper => by
        have mem := covers i hi (ac.trans_lt lower) upper
        apply (mem_insert.mp mem).resolve_left
        intro eqv
        rw [eqv] at lower upper
        have vc : v ≤ c := le_min upper.le (le_max_right _ _)
        exact (not_lt_of_ge vc) lower)
        (fun t ht => bound t ⟨ac.trans ht.1,ht.2⟩)
      calc (∑ i ∈ samples, weight i*width a b (value i))
           = (∑ i ∈ samples, weight i*width a c (value i))+
             (∑ i ∈ samples, weight i*width c b (value i)) := by
                rw [←Finset.sum_add_distrib]
                exact Finset.sum_congr rfl (fun i _ => by rw [width_split ac cb,mul_add])
           _ ≤ ceiling*(c-a)+ceiling*(b-c) := add_le_add left right
           _ = _ := by ring
  exact subdivide (samples.image value) ab (fun i hi _ _ => mem_image_of_mem _ hi) bound

/-- A signed threshold count can increase only where a negative term leaves.
    To bound it on [a,b), it suffices to test the left endpoint and those jumps. -/
theorem bound_of_negative_jumps {A : Type*} (samples : Finset A) (v w : A → ℝ)
    (ceiling a b : ℝ) (tested : ∀ t ∈ Set.Ico a b,
      (t=a ∨ ∃ i ∈ samples, w i<0 ∧ v i=t) →
      (∑ i ∈ samples, w i*(if t<v i then (1:ℝ) else 0)) ≤ ceiling) :
    ∀ t ∈ Set.Ico a b, (∑ i ∈ samples, w i*(if t<v i then (1:ℝ) else 0)) ≤ ceiling := by
  classical
  intro t ht
  let starts := insert a ((samples.filter (fun i => w i<0 ∧ a≤v i ∧ v i≤t)).image v)
  have ha : a ∈ starts := mem_insert_self _ _
  let q := starts.max' ⟨a,ha⟩
  have aq : a ≤ q := le_max' _ _ ha
  have qmem : q ∈ starts := max'_mem _ _
  have qt : q ≤ t := by
    rcases mem_insert.mp qmem with eq | mem
    · exact eq.trans_le ht.1
    · obtain ⟨i,hi,eq⟩ := mem_image.mp mem
      exact eq.symm.trans_le (mem_filter.mp hi).2.2.2
  have chosen : q=a ∨ ∃ i ∈ samples, w i<0 ∧ v i=q := by
    rcases mem_insert.mp qmem with eq | mem
    · exact Or.inl eq
    · obtain ⟨i,hi,eq⟩ := mem_image.mp mem
      exact Or.inr ⟨i,(mem_filter.mp hi).1,(mem_filter.mp hi).2.1,eq⟩
  apply le_trans _ (tested q ⟨aq,qt.trans_lt ht.2⟩ chosen)
  apply sum_le_sum
  intro i hi
  by_cases sign : 0 ≤ w i
  · apply mul_le_mul_of_nonneg_left _ sign
    by_cases present : t<v i
    · simp [present,qt.trans_lt present]
    · simp only [present,if_false]; split <;> norm_num
  · have same : (q<v i) = (t<v i) := by
      apply propext
      refine ⟨fun qv => ?_, fun tv => qt.trans_lt tv⟩
      by_contra! vt
      have mem : v i ∈ starts := mem_insert_of_mem (mem_image_of_mem _
        (mem_filter.mpr ⟨hi,lt_of_not_ge sign,(aq.trans qv.le),vt⟩))
      exact (not_lt_of_ge (le_max' _ _ mem)) qv
    simp only [same, le_refl]

/-- The actual geometric rank inequality is needed only at zero and the
    input shortfalls in [0,h). No target-slope tests or integration are used. -/
theorem rank_share_transfer {I J : Type} [Fintype I] [Fintype J] (m : I → ℕ)
    (x : ∀ i, Fin (m i) → ℝ) (y : J → ℝ) (s u h δ b : ℝ)
    (hu : 0 ≤ u) (hh : 0 ≤ h) (hd : δ < 1)
    (ni : 0 < ∑ i, (m i:ℝ)) (nj : 0 < (Fintype.card J:ℝ))
    (hsum : (∑ i, (m i : ℝ))*s ≤ ∑ i, ∑ j, x i j)
    (hle : ∀ i j, x i j ≤ s+u) (hy : ∀ j, s-h ≤ y j)
    (rank_bound : ∀ t ∈ Set.Ico (0:ℝ) h, (t=0 ∨ ∃ i j, s-x i j=t) →
      ((1-δ)/(Fintype.card J:ℝ))*(∑ j, if y j<s-t then (1:ℝ) else 0) ≤
        b+(4/(∑ i, (m i:ℝ)))*(∑ i, ∑ j, if x i j<s-t then (1:ℝ) else 0)) :
    s - (∑ j, y j)/(Fintype.card J:ℝ) ≤
      (b*h+4*(u*h/(u+h)))/(1-δ) := by
  classical
  let v : J ⊕ (Σ i, Fin (m i)) → ℝ :=
    Sum.elim (fun j => s-y j) (fun p => s-x p.1 p.2)
  let w : J ⊕ (Σ i, Fin (m i)) → ℝ :=
    Sum.elim (fun _ => (1-δ)/(Fintype.card J:ℝ)) (fun _ => -(4/(∑ i, (m i:ℝ))))
  have split_sum (f : ℝ → ℝ) :
      (∑ k, w k*f (v k)) = ((1-δ)/(Fintype.card J:ℝ))*(∑ j, f (s-y j)) -
        (4/(∑ i, (m i:ℝ)))*(∑ i, ∑ j, f (s-x i j)) := by
    rw [Fintype.sum_sum_type,Fintype.sum_sigma]
    simp only [v,w,Sum.elim_inl,Sum.elim_inr,neg_mul,Finset.sum_neg_distrib,Finset.mul_sum,sub_eq_add_neg]
  have test (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) h)
      (cut : t=0 ∨ ∃ k ∈ (univ : Finset (J ⊕ (Σ i, Fin (m i)))), w k<0 ∧ v k=t) :
      (∑ i, w i*(if t<v i then (1:ℝ) else 0)) ≤ b := by
    have only_input : t=0 ∨ ∃ i j, s-x i j=t := by
      rcases cut with start|⟨k,_,neg,eq⟩
      · exact Or.inl start
      rcases k with j|⟨i,j⟩
      · exact False.elim ((not_lt_of_ge (div_nonneg (sub_nonneg.mpr hd.le) nj.le)) neg)
      · exact Or.inr ⟨i,j,eq⟩
    rw [split_sum (fun z => if t<z then 1 else 0)]
    have flip (z : ℝ) : (t<s-z) = (z<s-t) := propext ⟨fun hz => by linarith,fun hz => by linarith⟩
    simp only [flip]
    linarith [rank_bound t ht only_input]
  have summed := finite_threshold_bound Finset.univ v w b hh (bound_of_negative_jumps _ _ _ _ _ _ test)
  rw [split_sum (width 0 h),sub_zero] at summed
  have each (j : J) : s-y j ≤ width 0 h (s-y j) := by
    simp only [width,sub_zero]
    exact le_min (by linarith [hy j]) (le_max_right _ _)
  have total := sum_le_sum (s:=univ) (fun (j : J) _ => each j)
  simp only [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul] at total
  have inputs : (∑ i, ∑ j, width 0 h (s-x i j)) ≤ (∑ i, (m i:ℝ))*(u*h/(u+h)) := by
    simpa only [width,sub_zero,max_comm (0:ℝ)] using
        IntegratedSlopeShare.integrated_share m x s u h hu hh hsum hle
  have hp : 0 < 1-δ := by linarith
  have left := mul_le_mul_of_nonneg_left total (div_nonneg hp.le nj.le)
  have right := mul_le_mul_of_nonneg_left inputs (div_nonneg (by norm_num : (0:ℝ)≤4) ni.le)
  apply (le_div_iff₀ hp).mpr
  calc _ = ((1-δ)/(Fintype.card J:ℝ))*((Fintype.card J:ℝ)*s-∑ j, y j) := by field_simp
       _ ≤ b*h+(4/(∑ i, (m i:ℝ)))*((∑ i, (m i:ℝ))*(u*h/(u+h))) := by linarith
       _ = _ := by field_simp [ni.ne']

#print axioms finite_threshold_bound
#print axioms bound_of_negative_jumps
#print axioms rank_share_transfer

end
end FiniteSlopeShare
