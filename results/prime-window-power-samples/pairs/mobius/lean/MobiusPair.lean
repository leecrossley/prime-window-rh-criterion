import MobiusAbsolute

open Finset ArithmeticFunction
namespace RiemannReduction.DivisorBand
noncomputable section

private def pairSlope : ℝ := (Real.log 3-c)/3

/-- Ratio at which the residual weights of an odd divisor and its double agree. -/
def pairRatio : ℝ := (2*c+Real.log 3-2*mainSlope)/pairSlope

private lemma ratio_bounds : 0 < pairSlope ∧ pairSlope ≤ 1 ∧ 28/9 ≤ pairRatio ∧ pairRatio < 4 := by
  have clo : 1/3 ≤ c := by unfold c; linarith [Real.log_two_gt_d9]
  have chi : c ≤ 7/20 := by unfold c; linarith [Real.log_two_lt_d9]
  have L := Real.log_three_gt_d9
  have U := Real.log_three_lt_d9
  have sp : 0 < pairSlope := by unfold pairSlope; linarith
  have su : pairSlope ≤ 1 := by unfold pairSlope; linarith
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
  · unfold pairRatio
    apply (le_div_iff₀ sp).mpr
    unfold pairSlope at *
    linarith
  · unfold pairRatio
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
  rw [residual_at_three lo hi,residual_at_one (by linarith) (by linarith),mul_sub pairSlope,pairRatio,
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

/-- All odd divisors in the h places immediately above the real crossing. -/
def pairAnchors (k h : ℕ) : Finset ℕ :=
  let start := ⌊(k:ℝ)^2/pairRatio⌋₊
  (Ioc start (start+h)).filter Odd

private lemma anchor_geometry {k h d : ℕ} (four : 4 ≤ k) (room : 108*h ≤ k^2)
    (hd : d ∈ pairAnchors k h) :
    k < d ∧ 2*d ≤ k^2 ∧ 3 ≤ (k:ℝ)^2/d ∧ (k:ℝ)^2/d < 4 ∧
      |tailTerm k d+tailTerm k (2*d)| ≤ 16*h/(k:ℝ)^2 := by
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
    ((mul_le_of_le_one_left gapPos su).trans gap)

/-- The pair contribution, computed using the actual weights and opposite Möbius signs. -/
theorem paired_sum_bound {k h : ℕ} (four : 4 ≤ k) (room : 108*h ≤ k^2) :
    |∑ d ∈ pairAnchors k h, (tailTerm k d+tailTerm k (2*d))| ≤ 16*(h:ℝ)^2/(k:ℝ)^2 := by
  have count : (pairAnchors k h).card ≤ h := by
    unfold pairAnchors
    exact (card_filter_le _ _).trans (by simp)
  have amount : 0 ≤ 16*(h:ℝ)/(k:ℝ)^2 := by positivity
  calc _ ≤ ∑ d ∈ pairAnchors k h, |tailTerm k d+tailTerm k (2*d)| := abs_sum_le_sum_abs _ _
       _ ≤ ∑ _d ∈ pairAnchors k h, (16*(h:ℝ)/(k:ℝ)^2) :=
         sum_le_sum (fun d hd => (anchor_geometry four room hd).2.2.2.2)
       _ = ((pairAnchors k h).card:ℝ)*(16*h/(k:ℝ)^2) := by simp
       _ ≤ (h:ℝ)*(16*h/(k:ℝ)^2) := mul_le_mul_of_nonneg_right (by exact_mod_cast count) amount
       _ = _ := by ring

/-- Remove the controlled odd divisors and their doubles from the signed tail. -/
def unpairedTail (k h : ℕ) : ℝ :=
  let anchors := pairAnchors k h
  ∑ d ∈ Ioc k (k^2) \ (anchors ∪ anchors.image (fun n => 2*n)), tailTerm k d

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

/-- A width of k times floor(sqrt(k)) costs at most 16k after pairing, at every large k. -/
theorem peel_pairs_at_square_root_cost {k : ℕ} (large : 108^2 ≤ k) :
    |largeDivisorSum k-unpairedTail k (k*k.sqrt)| ≤ 16*k := by
  have sq := Nat.sqrt_le' k
  have room := square_room large
  have four : 4 ≤ k := by norm_num at large; omega
  rw [paired_partition four room]
  apply (paired_sum_bound four room).trans
  have kp : 0 < (k:ℝ) := Nat.cast_pos.mpr (by omega)
  apply (div_le_iff₀ (sq_pos_of_pos kp)).mpr
  push_cast
  have sqR : (k.sqrt:ℝ)^2 ≤ k := by exact_mod_cast sq
  nlinarith [mul_le_mul_of_nonneg_left sqR (sq_nonneg (k:ℝ))]

/-- Before cancellation the same collection has absolute mass at least k floor(sqrt(k))/1728. -/
theorem paired_absolute_mass {k : ℕ} (large : 108^2 ≤ k) :
    (k:ℝ)*k.sqrt/1728 ≤
      ∑ d ∈ pairAnchors k (k*k.sqrt), (|tailTerm k d|+|tailTerm k (2*d)|) := by
  let h := k*k.sqrt
  let r := ⌊(k:ℝ)^2/pairRatio⌋₊
  let s := (Ioc r (r+h)).filter (fun d => Odd d ∧ Squarefree d)
  have four : 4 ≤ k := by norm_num at large; omega
  have s108 : 108 ≤ k.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using large)
  have room := square_room large
  have rl := ratio_bounds.2.2.1
  have rp : 0 < pairRatio := by linarith
  have xp : 0 ≤ (k:ℝ)^2 := sq_nonneg _
  have floor := Nat.floor_le (div_nonneg xp rp.le)
  have cap : r+h ≤ k^2 := by
    have hR : 108*(h:ℝ) ≤ (k:ℝ)^2 := by exact_mod_cast room
    have center : (k:ℝ)^2/pairRatio ≤ (k:ℝ)^2/2 :=
      div_le_div_of_nonneg_left xp (by norm_num) (by linarith)
    have rR : (r:ℝ) ≤ (k:ℝ)^2/2 := floor.trans center
    exact_mod_cast (show (r:ℝ)+h ≤ (k:ℝ)^2 by linarith)
  have density := odd_squarefree_count (Nat.le_add_right r h) cap (by omega : 3 ≤ k)
  change _ ≤ (s.card:ℝ) at density
  push_cast at density
  have hk : 108*(k:ℝ) ≤ h := by
    exact_mod_cast (show 108*k ≤ h by dsimp [h]; simpa [Nat.mul_comm] using Nat.mul_le_mul_left k s108)
  have kpos : (1:ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have many : (h:ℝ)/36 ≤ s.card := by linarith
  have subset : s ⊆ pairAnchors k h := fun d hd =>
    mem_filter.mpr ⟨(mem_filter.mp hd).1,(mem_filter.mp hd).2.1⟩
  have value : (∑ _d ∈ s, (1/48:ℝ)) ≤ ∑ d ∈ s, (|tailTerm k d|+|tailTerm k (2*d)|) := by
    apply sum_le_sum
    intro d hd
    obtain ⟨_,odd,sq⟩ := mem_filter.mp hd
    obtain ⟨_,_,lo,hi,_⟩ := anchor_geometry four room (subset hd)
    have mu : |(ArithmeticFunction.moebius (2*d):ℝ)| = 1 := by
      rw [isMultiplicative_moebius.map_mul_of_coprime odd.coprime_two_left,moebius_apply_prime Nat.prime_two]
      have absd : |(ArithmeticFunction.moebius d:ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree sq
      push_cast
      simpa using absd
    have arg : (k:ℝ)^2/↑(2*d:ℕ) = (k:ℝ)^2/d/2 := by push_cast; ring
    have weight := residual_first_bin (t := (k:ℝ)^2/d/2) (by linarith) (by linarith)
    have eq : |tailTerm k (2*d)| = residual mainSlope ((k:ℝ)^2/d/2) := by
      rw [tailTerm,abs_mul,mu,one_mul,arg,abs_of_nonneg (by linarith)]
    rw [eq]
    linarith [abs_nonneg (tailTerm k d)]
  have full := sum_le_sum_of_subset_of_nonneg (f := fun d => |tailTerm k d|+|tailTerm k (2*d)|)
    subset (fun d _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  simp only [sum_const,nsmul_eq_mul] at value
  change _ ≤ ∑ d ∈ pairAnchors k h, (|tailTerm k d|+|tailTerm k (2*d)|)
  have id : (h:ℝ) = (k:ℝ)*k.sqrt := by simp [h]
  linarith

#print axioms paired_sum_bound
#print axioms peel_pairs_at_square_root_cost
#print axioms paired_absolute_mass
end
end RiemannReduction.DivisorBand
