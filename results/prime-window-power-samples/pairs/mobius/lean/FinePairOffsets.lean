import MobiusPair

/-! Retain the actual slope and sum the distances of the odd divisors from the crossing. -/

open Finset ArithmeticFunction
namespace RiemannReduction.DivisorBand.FinePair
noncomputable section

private def pairSlope : ℝ := (Real.log 3-c)/3

private lemma ratio_bounds : 0 < pairSlope ∧ pairSlope ≤ 13/50 ∧ 28/9 ≤ pairRatio ∧ pairRatio < 4 := by
  have clo : 1/3 ≤ c := by unfold c; linarith [Real.log_two_gt_d9]
  have chi : c ≤ 7/20 := by unfold c; linarith [Real.log_two_lt_d9]
  have L := Real.log_three_gt_d9
  have U := Real.log_three_lt_d9
  have sp : 0 < pairSlope := by unfold pairSlope; linarith
  have su : pairSlope ≤ 13/50 := by unfold pairSlope; linarith
  have slope : mainSlope = c*(Real.eulerMascheroniConstant+1-c) := by
    unfold mainSlope c logMoment
    ring
  have ap : mainSlope ≤ (4/3)*c := by
    rw [slope,mul_comm (4/3:ℝ)]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have al : (23/20)*c ≤ mainSlope := by
    rw [slope,mul_comm (23/20:ℝ)]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  refine ⟨sp,su,?_,?_⟩
  · change _ ≤ (2*c+Real.log 3-2*mainSlope)/pairSlope
    apply (le_div_iff₀ sp).mpr
    unfold pairSlope at *
    linarith
  · change (2*c+Real.log 3-2*mainSlope)/pairSlope < _
    apply (div_lt_iff₀ sp).mpr
    unfold pairSlope at *
    linarith

private lemma residual_at_one {t : ℝ} (lo : 1 ≤ t) (hi : t < 2) :
    residual mainSlope t = c*t-mainSlope := by
  have fl : ⌊t⌋₊ = 1 := (Nat.floor_eq_iff (by linarith)).mpr ⟨by simpa using lo,by norm_num; linarith⟩
  simp [residual,dilate,fl,ArithmeticFunction.log_apply,harmonic]

private lemma first_slope {v : ℝ} (lo : 1 ≤ v) (hi : v < 2) : window v = v-1 := by
  rw [window,ThetaTransfer.tent_pieces]
  split_ifs <;> linarith

private lemma residual_at_three {t : ℝ} (lo : 3 ≤ t) (hi : t < 4) :
    residual mainSlope t = (11/6)*c*t - 2*c*(t/2-1) - Real.log 3*(t/3-1) - 3*mainSlope := by
  have fl : ⌊t⌋₊ = 3 := (Nat.floor_eq_iff (by linarith)).mpr ⟨by norm_num; linarith,by norm_num; linarith⟩
  have w2 := first_slope (v := t/2) (by linarith) (by linarith)
  have w3 := first_slope (v := t/3) (by linarith) (by linarith)
  unfold residual dilate
  rw [fl,show (Icc 1 3 : Finset ℕ) = {1,2,3} by decide]
  norm_num [ArithmeticFunction.log_apply,harmonic,w2,w3,c]
  ring

private lemma residual_difference {t : ℝ} (lo : 3 ≤ t) (hi : t < 4) :
    residual mainSlope t - residual mainSlope (t/2) = pairSlope*(pairRatio-t) := by
  rw [residual_at_three lo hi,residual_at_one (by linarith) (by linarith),mul_sub pairSlope,show pairRatio = (2*c+Real.log 3-2*mainSlope)/pairSlope from rfl,
    mul_div_cancel₀ _ ratio_bounds.1.ne']
  unfold pairSlope
  ring

private lemma pair_eq {k d : ℕ} (odd : Odd d) (lo : 3 ≤ (k:ℝ)^2/d) (hi : (k:ℝ)^2/d < 4) :
    tailTerm k d+tailTerm k (2*d) =
      (ArithmeticFunction.moebius d:ℝ)*(pairSlope*(pairRatio-(k:ℝ)^2/d)) := by
  have mu : ArithmeticFunction.moebius (2*d) = -ArithmeticFunction.moebius d := by
    rw [isMultiplicative_moebius.map_mul_of_coprime odd.coprime_two_left,
      moebius_apply_prime Nat.prime_two,neg_one_mul]
  rw [← residual_difference lo hi]
  unfold tailTerm
  rw [mu]
  push_cast
  rw [show (k:ℝ)^2/(2*d)=(k:ℝ)^2/d/2 by ring]
  ring

private lemma anchor_geometry {k h d : ℕ} (four : 4 ≤ k) (room : 108*h ≤ k^2)
    (hd : d ∈ pairAnchors k h) :
    k < d ∧ 2*d ≤ k^2 ∧ 3 ≤ (k:ℝ)^2/d ∧ (k:ℝ)^2/d < 4 ∧
      |tailTerm k d+tailTerm k (2*d)| ≤ (104/25)*h/(k:ℝ)^2 := by
  obtain ⟨sp,su,rl,ru⟩ := ratio_bounds
  have rp : 0 < pairRatio := by linarith
  have kp : 0 < (k:ℝ) := Nat.cast_pos.mpr (by omega)
  have xp : 0 < (k:ℝ)^2 := by positivity
  let center := (k:ℝ)^2/pairRatio
  have centerPos : 0 ≤ center := (div_pos xp rp).le
  have id : center*pairRatio = (k:ℝ)^2 := div_mul_cancel₀ _ rp.ne'
  have size : (k:ℝ)^2 ≤ 4*center := by nlinarith [mul_le_mul_of_nonneg_left ru.le centerPos]
  obtain ⟨mem,odd⟩ := mem_filter.mp hd
  obtain ⟨below,above⟩ := mem_Ioc.mp mem
  have left : center < (d:ℝ) := (Nat.floor_lt centerPos).mp below
  have right : (d:ℝ) ≤ center+h := by
    change d ≤ ⌊center⌋₊+h at above
    have le : (d:ℝ) ≤ (⌊center⌋₊:ℝ)+h := by exact_mod_cast above
    linarith [Nat.floor_le centerPos]
  have dp : 0 < (d:ℝ) := centerPos.trans_lt left
  have roomR : 108*(h:ℝ) ≤ (k:ℝ)^2 := by exact_mod_cast room
  have tlo : 3 ≤ (k:ℝ)^2/d := (le_div_iff₀ dp).mpr (by
    nlinarith [mul_le_mul_of_nonneg_left (show 1/9 ≤ pairRatio-3 by linarith) centerPos])
  have xt : (k:ℝ)^2 < pairRatio*d := by nlinarith [mul_lt_mul_of_pos_right left rp]
  have thi : (k:ℝ)^2/d < 4 := ((div_lt_iff₀ dp).mpr (by nlinarith [mul_lt_mul_of_pos_right ru dp]))
  have dgt : k < d := by
    have k4 : (4:ℝ) ≤ k := by exact_mod_cast four
    exact_mod_cast (show (k:ℝ) < d by nlinarith [mul_le_mul_of_nonneg_right k4 kp.le])
  have dcap : 2*d ≤ k^2 := by
    exact_mod_cast (show 2*(d:ℝ) ≤ (k:ℝ)^2 by linarith [(le_div_iff₀ dp).mp tlo])
  refine ⟨dgt,dcap,tlo,thi,?_⟩
  have gapPos : 0 ≤ pairRatio-(k:ℝ)^2/d := sub_nonneg.mpr ((div_le_iff₀ dp).mpr xt.le)
  have diff : pairRatio-(k:ℝ)^2/d = (pairRatio*((d:ℝ)-center))/d := by
    apply (eq_div_iff dp.ne').mpr
    rw [sub_mul,div_mul_cancel₀ _ dp.ne']
    nlinarith
  have gap : pairRatio-(k:ℝ)^2/d ≤ 16*h/(k:ℝ)^2 := by
    rw [diff]
    calc _ ≤ (4*h)/(d:ℝ) := div_le_div_of_nonneg_right
               (mul_le_mul ru.le (by linarith) (by linarith) (by norm_num)) dp.le
         _ ≤ _ := (div_le_div_iff₀ dp xp).mpr (by
           nlinarith [mul_le_mul_of_nonneg_right ((div_lt_iff₀ dp).mp thi).le (Nat.cast_nonneg (α := ℝ) h)])
  rw [pair_eq odd tlo thi,abs_mul,abs_of_nonneg (mul_nonneg sp.le gapPos)]
  have mu : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  exact (mul_le_of_le_one_left (mul_nonneg sp.le gapPos) mu).trans
    (calc pairSlope*(pairRatio-(k:ℝ)^2/d) ≤ (13/50)*(16*h/(k:ℝ)^2) :=
       mul_le_mul su gap gapPos (by norm_num)
     _ = _ := by ring)

private lemma paired_partition {k h : ℕ} (four : 4 ≤ k) (room : 108*h ≤ k^2) :
    largeDivisorSum k-unpairedTail k h =
      ∑ d ∈ pairAnchors k h, (tailTerm k d+tailTerm k (2*d)) := by
  let s := pairAnchors k h
  have members {d : ℕ} (hd : d ∈ s) :
      d ∈ Ioc k (k^2) ∧ 2*d ∈ Ioc k (k^2) := by
    obtain ⟨lo,hi,_⟩ := anchor_geometry four room hd
    exact ⟨mem_Ioc.mpr ⟨lo,by omega⟩,mem_Ioc.mpr ⟨by omega,hi⟩⟩
  have inc : s ∪ s.image (fun n => 2*n) ⊆ Ioc k (k^2) := by
    intro d hd
    rcases mem_union.mp hd with h | h
    · exact (members h).1
    · obtain ⟨e,he,rfl⟩ := mem_image.mp h
      exact (members he).2
  have dis : Disjoint s (s.image (fun n => 2*n)) := by
    apply disjoint_left.mpr
    intro d hd he
    obtain ⟨e,_,rfl⟩ := mem_image.mp he
    obtain ⟨q,eq⟩ := (mem_filter.mp hd).2
    omega
  have split := sum_sdiff (f := tailTerm k) inc
  rw [sum_union dis,sum_image (by intro a _ b _ eq; change 2*a = 2*b at eq; omega)] at split
  change (∑ d ∈ Ioc k (k^2), tailTerm k d) -
    (∑ d ∈ Ioc k (k^2) \ (s ∪ s.image (fun n => 2*n)), tailTerm k d) = _
  rw [sum_add_distrib]
  change _ = (∑ d ∈ s, tailTerm k d) + ∑ d ∈ s, tailTerm k (2*d)
  linarith

private lemma square_room {k : ℕ} (large : 108^2 ≤ k) : 108*(k*k.sqrt) ≤ k^2 := by
  have s108 : 108 ≤ k.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using large)
  have bound : 108*k.sqrt ≤ k := (Nat.mul_le_mul_right k.sqrt s108).trans (Nat.sqrt_le k)
  rw [show 108*(k*k.sqrt) = k*(108*k.sqrt) by ring,pow_two]
  exact Nat.mul_le_mul_left k bound

private def oddOffsets (s h : ℕ) : ℕ :=
  ∑ d ∈ (Ioc s (s+h)).filter Odd, (d-s)

private theorem oddOffsets_succ (s h : ℕ) :
    oddOffsets s (h+1) = oddOffsets s h + if Odd (s+h+1) then h+1 else 0 := by
  have interval : Ioc s (s+(h+1)) = insert (s+h+1) (Ioc s (s+h)) := by
    ext a
    simp only [mem_Ioc,mem_insert]
    omega
  have fresh : s+h+1 ∉ Ioc s (s+h) := by simp
  have off : s+h+1-s = h+1 := by omega
  unfold oddOffsets
  simp only [sum_filter]
  rw [interval, sum_insert fresh, off, add_comm]

private theorem oddOffsets_bound (s h : ℕ) : 4 * oddOffsets s h ≤ (h+1)^2 := by
  induction h using Nat.twoStepInduction with
  | zero => simp [oddOffsets]
  | one =>
    have z : oddOffsets s 0 = 0 := by simp [oddOffsets]
    rw [show 1 = 0+1 by decide, oddOffsets_succ, z]
    split <;> decide
  | more n ih _ =>
    have excl : ¬(Odd (s+n+1) ∧ Odd (s+(n+1)+1)) := by
      rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
      omega
    have step : oddOffsets s (n+2) ≤ oddOffsets s n+(n+2) := by
      change oddOffsets s (n+1+1) ≤ oddOffsets s n+(n+2)
      have h1 := oddOffsets_succ s n
      have h2 := oddOffsets_succ s (n+1)
      by_cases a : Odd (s+n+1) <;> by_cases b : Odd (s+(n+1)+1)
      · exact (excl ⟨a,b⟩).elim
      · rw [if_pos a] at h1; rw [if_neg b] at h2; omega
      · rw [if_neg a] at h1; rw [if_pos b] at h2; omega
      · rw [if_neg a] at h1; rw [if_neg b] at h2; omega
    nlinarith only [ih, step]

theorem paired_cost_with_offsets {k h : ℕ} (four : 4 ≤ k) (room : 108*h ≤ k^2) :
    |largeDivisorSum k - unpairedTail k h| ≤ (26/25)*((h:ℝ)+1)^2/(k:ℝ)^2 := by
  let s := ⌊(k:ℝ)^2/pairRatio⌋₊
  have kp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have each (d : ℕ) (hd : d ∈ pairAnchors k h) :
      |tailTerm k d+tailTerm k (2*d)| ≤ ((104/25)/(k:ℝ)^2)*((d-s : ℕ):ℝ) := by
    change d ∈ (Ioc s (s+h)).filter Odd at hd
    obtain ⟨mem,odd⟩ := mem_filter.mp hd
    obtain ⟨lo,hi⟩ := mem_Ioc.mp mem
    have off : d-s ≤ h := by omega
    have shorter : d ∈ pairAnchors k (d-s) :=
      mem_filter.mpr ⟨mem_Ioc.mpr ⟨lo, by change d ≤ s+(d-s); omega⟩,odd⟩
    have ht := (anchor_geometry four ((Nat.mul_le_mul_left _ off).trans room) shorter).2.2.2.2
    convert ht using 1
    ring
  have bound : (4 : ℝ) * oddOffsets s h ≤ ((h:ℝ)+1)^2 := by exact_mod_cast oddOffsets_bound s h
  rw [paired_partition four room]
  calc _ ≤ ∑ d ∈ pairAnchors k h, |tailTerm k d+tailTerm k (2*d)| := abs_sum_le_sum_abs _ _
       _ ≤ ∑ d ∈ pairAnchors k h, ((104/25)/(k:ℝ)^2)*((d-s : ℕ):ℝ) := sum_le_sum each
       _ = ((104/25)/(k:ℝ)^2)*(oddOffsets s h : ℝ) := by
         rw [← mul_sum]
         unfold oddOffsets
         simp only [Nat.cast_sum]
         rfl
       _ ≤ _ := by
         rw [div_mul_eq_mul_div]
         exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

theorem paired_cost_nine_eighths {k : ℕ} (late : 108^2 ≤ k) :
    |largeDivisorSum k-unpairedTail k (k*k.sqrt)| ≤ (9/8)*(k:ℝ) := by
  have four : 4 ≤ k := by norm_num at late; omega
  have coarse := paired_cost_with_offsets four (square_room late)
  have kp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have sr : 108 ≤ k.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using late)
  have sr1 : (1:ℝ) ≤ k.sqrt := by exact_mod_cast (show 1 ≤ k.sqrt by omega)
  have large : (100:ℝ) ≤ k := by exact_mod_cast (show 100 ≤ k by norm_num at late; omega)
  have hbig : (100:ℝ) ≤ (k:ℝ)*k.sqrt := by nlinarith [mul_le_mul_of_nonneg_left sr1 kp.le]
  have hnext : (k:ℝ)*k.sqrt+1 ≤ (101/100)*((k:ℝ)*k.sqrt) := by linarith
  have squares := pow_le_pow_left₀ (by positivity : 0 ≤ (k:ℝ)*k.sqrt+1) hnext 2
  have root : (k.sqrt:ℝ)^2 ≤ k := by exact_mod_cast Nat.sqrt_le' k
  have key := mul_le_mul_of_nonneg_left root (sq_nonneg (k:ℝ))
  apply coarse.trans ((div_le_iff₀ (sq_pos_of_pos kp)).2 ?_)
  push_cast
  nlinarith only [squares,key, mul_nonneg kp.le (sq_nonneg (k:ℝ))]

end
end RiemannReduction.DivisorBand.FinePair
