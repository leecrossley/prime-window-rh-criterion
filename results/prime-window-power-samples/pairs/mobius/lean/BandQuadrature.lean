import DivisorBand

open Finset MeasureTheory
namespace RiemannReduction.DivisorBand
noncomputable section

private def piece (A B t : ℝ) := (A/t+B)*Real.log t
private def slope (A B t : ℝ) := A*(1-Real.log t)/t^2+B/t

private lemma piece_deriv (A B : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (piece A B) (slope A B t) t := by
  have d := (((hasDerivAt_const t A).div (hasDerivAt_id t) ht.ne').add_const B).mul
    (Real.hasDerivAt_log ht.ne')
  convert d using 1 <;> try rfl
  all_goals try dsimp [piece,slope]
  all_goals field_simp [ht.ne']; ring

private lemma slope_deriv (A B : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (slope A B) (A*(2*Real.log t-3)/t^3-B/t^2) t := by
  have d := ((((Real.hasDerivAt_log ht.ne').const_sub 1).const_mul A).div
    ((hasDerivAt_id t).pow 2) (pow_ne_zero _ ht.ne')).add
    ((hasDerivAt_const t B).div (hasDerivAt_id t) ht.ne')
  convert d using 1 <;> try rfl
  all_goals try dsimp [slope]
  all_goals field_simp [ht.ne']; ring

private lemma piece_int (A B : ℝ) {l u : ℝ} (hl : 0 < l) (hu : 0 < u) :
    IntervalIntegrable (piece A B) volume l u := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  apply (piece_deriv A B ((lt_min hl hu).trans_le ht.1)).continuousAt.continuousWithinAt

private lemma trap_as_sum (f : ℝ → ℝ) {p q : ℕ} (lt : p < q) :
    trapezoidal_integral f (q-p) p q =
      (∑ n ∈ Ioc p q, f n)+(f p-f q)/2 := by
  have step : ((q:ℝ)-p)/(↑(q-p:ℕ):ℝ) = 1 := by
    rw [Nat.cast_sub lt.le,div_self (sub_ne_zero.mpr (Nat.cast_lt.mpr lt).ne')]
  have split : ∑ n ∈ Ioc p q, f n = (∑ n ∈ Ico (p+1) q, f n)+f q := by
    have eq : Ioc p q = Ico (p+1) (q+1) := by ext n; simp only [mem_Ioc,mem_Ico]; omega
    rw [eq,sum_Ico_succ_top (by omega)]
  rw [split,sum_Ico_eq_sum_range,trapezoidal_integral,step,one_mul]
  have len : q-(p+1) = q-p-1 := by omega
  rw [len]
  have same : ∑ k ∈ range (q-p-1), f (p+(k+1)*((q:ℝ)-p)/↑(q-p:ℕ)) =
      ∑ k ∈ range (q-p-1), f (↑(p+1+k:ℕ):ℝ) := by
    apply sum_congr rfl
    intro k _
    congr 1
    rw [mul_div_assoc,step,mul_one]; push_cast; ring
  rw [same]; ring

/-- On an integral mesh above x/8, the trapezoidal error is bounded independently
of x. The logarithmic band has the form (A/t+B) log t on each smooth piece. -/
private lemma piece_mesh {x A B : ℝ} {p q : ℕ} (large : 16 ≤ x) (lt : p < q)
    (start : x/8 ≤ p) (stop : (q:ℝ) ≤ x) (smallA : |A| ≤ x) (smallB : |B| ≤ 2) :
    |(∑ n ∈ Ioc p q, piece A B n)+(piece A B p-piece A B q)/2 -
      ∫ t in (p:ℝ)..q, piece A B t| ≤ 32 := by
  let S := Set.uIcc (p:ℝ) q
  have pq : (p:ℝ) < q := Nat.cast_lt.mpr lt
  have closed : IsClosed S := isClosed_Icc
  have unique : UniqueDiffOn ℝ S := by rw [show S = Set.Icc (p:ℝ) q from Set.uIcc_of_le pq.le]; exact uniqueDiffOn_Icc pq
  have size {t : ℝ} (ht : t ∈ S) : x/8 ≤ t ∧ 1 ≤ t := by
    rw [show S = Set.Icc (p:ℝ) q from Set.uIcc_of_le pq.le] at ht
    exact ⟨start.trans ht.1,by linarith [ht.1]⟩
  have diff : DifferentiableOn ℝ (piece A B) S := fun t ht =>
    (piece_deriv A B (show 0<t by linarith [(size ht).2])).differentiableAt.differentiableWithinAt
  have slopeEq : Set.EqOn (derivWithin (piece A B) S) (slope A B) S := fun t ht =>
    (piece_deriv A B (show 0<t by linarith [(size ht).2])).hasDerivWithinAt.derivWithin (unique t ht)
  have diff2 : DifferentiableOn ℝ (derivWithin (piece A B) S) S := by
    apply DifferentiableOn.congr _ slopeEq
    intro t ht
    exact (slope_deriv A B (show 0<t by linarith [(size ht).2])).differentiableAt.differentiableWithinAt
  have bound (t : ℝ) : |iteratedDerivWithin 2 (piece A B) S t| ≤ 384/x := by
    rw [iteratedDerivWithin_succ,iteratedDerivWithin_one]
    by_cases ht : t ∈ S
    · obtain ⟨lower,t1⟩ := size ht
      have tp : 0 < t := by linarith
      rw [derivWithin_congr slopeEq (slopeEq ht),(slope_deriv A B tp).hasDerivWithinAt.derivWithin (unique t ht)]
      have lg : |2*Real.log t-3| ≤ 5*t := abs_le.mpr
        ⟨by linarith [Real.log_nonneg t1],by linarith [Real.log_le_self tp.le]⟩
      calc _ ≤ |A*(2*Real.log t-3)/t^3| + |B/t^2| := by
               simpa only [sub_zero,zero_sub,abs_neg] using
                 abs_sub_le (A*(2*Real.log t-3)/t^3) 0 (B/t^2)
           _ = |A| * |2*Real.log t-3| /t^3 + |B| /t^2 := by
               rw [abs_div,abs_mul,abs_div,abs_pow,abs_pow,abs_of_pos tp]
           _ ≤ x*(5*t)/t^3+2/t^2 := add_le_add
               (div_le_div_of_nonneg_right (mul_le_mul smallA lg (abs_nonneg _) (by linarith)) (by positivity))
               (div_le_div_of_nonneg_right smallB (by positivity))
           _ = (5*x+2)/t^2 := by field_simp
           _ ≤ 384/x := by
               apply (div_le_div_iff₀ (by positivity) (by linarith)).mpr
               have sq := pow_le_pow_left₀ (show 0 ≤ x/8 by linarith) lower 2
               nlinarith [mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ x-2 by linarith)]
    · rw [derivWithin_zero_of_notMem_closure (show t ∉ closure S by simpa only [closed.closure_eq] using ht),abs_zero]
      positivity
  have rule := trapezoidal_error_le diff diff2 bound (Nat.sub_pos_of_lt lt)
  rw [trapezoidal_error,trap_as_sum _ lt,abs_of_pos (sub_pos.mpr pq),Nat.cast_sub lt.le] at rule
  apply rule.trans
  have xp : 0 < x := by linarith
  have dp : 0 < (q:ℝ)-p := sub_pos.mpr pq
  calc _ = 32*((q:ℝ)-p)/x := by field_simp; ring
       _ ≤ _ := (div_le_iff₀ xp).mpr (by linarith [Nat.cast_nonneg (α := ℝ) p])

private lemma log_sum_pieces {x : ℝ} (xp : 0 ≤ x) :
    dilate ArithmeticFunction.log window x =
      (∑ n ∈ Ioc ⌊x/4⌋₊ ⌊x/2⌋₊, piece (-x/2) 2 n) +
      ∑ n ∈ Ioc ⌊x/2⌋₊ ⌊x⌋₊, piece x (-1) n := by
  let f (n : ℕ) := Real.log n*window (x/n)
  have am : ⌊x/4⌋₊ ≤ ⌊x/2⌋₊ := Nat.floor_mono (by linarith)
  have mb : ⌊x/2⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
  have first : ∑ n ∈ Ioc 0 ⌊x/4⌋₊, f n = 0 := by
    apply sum_eq_zero
    intro n hn
    obtain ⟨np,cap⟩ := mem_Ioc.mp hn
    have pos : 0 < (n:ℝ) := Nat.cast_pos.mpr np
    have nr := (Nat.le_floor_iff (show 0 ≤ x/4 by linarith)).mp cap
    have one : 1 ≤ (x/n)/4 := by rw [le_div_iff₀ (by norm_num),le_div_iff₀ pos]; linarith
    simp [f,window,ThetaTransfer.tent_pieces,one]
  have value : dilate ArithmeticFunction.log window x = ∑ n ∈ Ioc 0 ⌊x⌋₊, f n := by
    unfold dilate
    congr 1
  rw [value,← sum_Ioc_consecutive f (Nat.zero_le _) mb,← sum_Ioc_consecutive f (Nat.zero_le _) am,first,zero_add]
  congr 1
  · apply sum_congr rfl
    intro n hn
    obtain ⟨lo,hi⟩ := mem_Ioc.mp hn
    have lo' := (Nat.floor_lt (show 0 ≤ x/4 by linarith)).mp lo
    have hi' := (Nat.le_floor_iff (show 0 ≤ x/2 by linarith)).mp hi
    have np : 0 < (n:ℝ) := by linarith
    have one : ¬1 ≤ (x/n)/4 := by rw [not_le,div_lt_iff₀ (by norm_num),div_lt_iff₀ np]; linarith
    have half : 1/2 ≤ (x/n)/4 := by rw [le_div_iff₀ (by norm_num),le_div_iff₀ np]; linarith
    simp only [f,window,ThetaTransfer.tent_pieces,if_neg one,if_pos half,piece]
    ring
  · apply sum_congr rfl
    intro n hn
    obtain ⟨lo,hi⟩ := mem_Ioc.mp hn
    have lo' := (Nat.floor_lt (show 0 ≤ x/2 by linarith)).mp lo
    have hi' := (Nat.le_floor_iff xp).mp hi
    have np : 0 < (n:ℝ) := by linarith
    have half : ¬1/2 ≤ (x/n)/4 := by rw [not_le,div_lt_iff₀ (by norm_num),div_lt_iff₀ np]; linarith
    have one : ¬1 ≤ (x/n)/4 := by linarith
    have fourth : 1/4 ≤ (x/n)/4 := by rw [le_div_iff₀ (by norm_num),le_div_iff₀ np]; linarith
    simp only [f,window,ThetaTransfer.tent_pieces,if_neg one,if_neg half,if_pos fourth,piece]
    ring

private lemma tip_bound {t : ℝ} (t1 : 1 ≤ t) (A B : ℝ) :
    |piece A B t| ≤ |A+B*t| := by
  have tp : 0 < t := by linarith
  have eq : piece A B t = (A+B*t)*(Real.log t/t) := by unfold piece; field_simp
  rw [eq,abs_mul,abs_of_nonneg (div_nonneg (Real.log_nonneg t1) tp.le)]
  exact mul_le_of_le_one_right (abs_nonneg _) ((div_le_one tp).mpr (Real.log_le_self tp.le))

private lemma short_int {f : ℝ → ℝ} {a b M : ℝ} (ab : a ≤ b) (length : b-a ≤ 1) (pos : 0 ≤ M)
    (bound : ∀ t ∈ Set.Icc a b, |f t| ≤ M) : |∫ t in a..b, f t| ≤ M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := f) (C := M)
    (fun t ht => by
      rw [Set.uIoc_of_le ab] at ht
      exact (Real.norm_eq_abs _).trans_le (bound t ⟨ht.1.le,ht.2⟩))
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ab)] at h
  exact h.trans (mul_le_of_le_one_right pos length)

private lemma sum_integral_error {x : ℝ} (large : 16 ≤ x) :
    |dilate ArithmeticFunction.log window x -
      ((∫ t in x/4..x/2, piece (-x/2) 2 t) + ∫ t in x/2..x, piece x (-1) t)| ≤ 73 := by
  let a := ⌊x/4⌋₊
  let m := ⌊x/2⌋₊
  let b := ⌊x⌋₊
  let L := piece (-x/2) 2
  let R := piece x (-1)
  have a0 : (a:ℝ) ≤ x/4 := Nat.floor_le (by linarith)
  have m0 : (m:ℝ) ≤ x/2 := Nat.floor_le (by linarith)
  have b0 : (b:ℝ) ≤ x := Nat.floor_le (by linarith)
  have a1 : x/4 < (a:ℝ)+1 := Nat.lt_floor_add_one _
  have m1 : x/2 < (m:ℝ)+1 := Nat.lt_floor_add_one _
  have b1 : x < (b:ℝ)+1 := Nat.lt_floor_add_one _
  have am : a < m := Nat.cast_lt.mp (show (a:ℝ) < m by linarith)
  have mb : m < b := Nat.cast_lt.mp (show (m:ℝ) < b by linarith)
  have lowA (t : ℝ) (ht : t ∈ Set.Icc (a:ℝ) (x/4)) : |L t| ≤ 2 := by
    apply (tip_bound (by linarith [ht.1] : 1 ≤ t) _ _).trans
    exact abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have lowB (t : ℝ) (ht : t ∈ Set.Icc (b:ℝ) x) : |R t| ≤ 1 := by
    apply (tip_bound (by linarith [ht.1] : 1 ≤ t) _ _).trans
    exact abs_le.mpr ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have mid (t : ℝ) (ht : t ∈ Set.Icc (m:ℝ) (x/2)) : |R t-L t| ≤ 3 := by
    have eq : R t-L t = piece (3*x/2) (-3) t := by dsimp [R,L,piece]; ring
    rw [eq]
    apply (tip_bound (by linarith [ht.1] : 1 ≤ t) _ _).trans
    exact abs_le.mpr ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have errA := piece_mesh (A := -x/2) (B := 2) large am (by linarith) (by linarith)
    (abs_le.mpr ⟨by linarith,by linarith⟩) (by norm_num)
  have errB := piece_mesh (A := x) (B := -1) large mb (by linarith) b0
    (le_of_eq (abs_of_nonneg (by linarith))) (by norm_num)
  change |(∑ n ∈ Ioc a m, L n)+(L a-L m)/2-(∫ t in (a:ℝ)..m,L t)| ≤ 32 at errA
  change |(∑ n ∈ Ioc m b, R n)+(R m-R b)/2-(∫ t in (m:ℝ)..b,R t)| ≤ 32 at errB
  have ea := short_int a0 (by linarith) (by norm_num : (0:ℝ) ≤ 2) lowA
  have eb := short_int b0 (by linarith) (by norm_num : (0:ℝ) ≤ 1) lowB
  have em := short_int m0 (by linarith) (by norm_num : (0:ℝ) ≤ 3) mid
  have iL {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : IntervalIntegrable L volume s t := piece_int _ _ hs ht
  have iR {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : IntervalIntegrable R volume s t := piece_int _ _ hs ht
  have el : (∫ t in (a:ℝ)..m,L t) = (∫ t in (a:ℝ)..x/4,L t) +
      (∫ t in x/4..x/2,L t)-(∫ t in (m:ℝ)..x/2,L t) := by
    have u := intervalIntegral.integral_add_adjacent_intervals (iL (s:=a) (t:=x/4) (by linarith) (by linarith))
      (iL (t:=x/2) (by linarith) (by linarith))
    have v := intervalIntegral.integral_add_adjacent_intervals (iL (s:=a) (t:=m) (by linarith) (by linarith))
      (iL (t:=x/2) (by linarith) (by linarith))
    linarith
  have er : (∫ t in (m:ℝ)..b,R t) = (∫ t in (m:ℝ)..x/2,R t) +
      (∫ t in x/2..x,R t)-(∫ t in (b:ℝ)..x,R t) := by
    have u := intervalIntegral.integral_add_adjacent_intervals (iR (s:=m) (t:=x/2) (by linarith) (by linarith))
      (iR (t:=x) (by linarith) (by linarith))
    have v := intervalIntegral.integral_add_adjacent_intervals (iR (s:=m) (t:=b) (by linarith) (by linarith))
      (iR (t:=x) (by linarith) (by linarith))
    linarith
  rw [intervalIntegral.integral_sub (iR (by linarith) (by linarith)) (iL (by linarith) (by linarith))] at em
  rw [log_sum_pieces (by linarith)]
  change |(∑ n ∈ Ioc a m,L n)+(∑ n ∈ Ioc m b,R n)-((∫ t in x/4..x/2,L t)+∫ t in x/2..x,R t)| ≤ 73
  have va := lowA a ⟨le_rfl,a0⟩
  have vb := lowB b ⟨le_rfl,b0⟩
  have vm := mid m ⟨le_rfl,m0⟩
  simp only [abs_le] at errA errB ea eb em va vb vm ⊢
  constructor <;> linarith

private def primitive (A B t : ℝ) := A*(Real.log t)^2/2+B*(t*Real.log t-t)

private lemma piece_integral (A B : ℝ) {l u : ℝ} (hl : 0 < l) (hu : 0 < u) :
    (∫ t in l..u, piece A B t) = primitive A B u-primitive A B l := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (piece_int A B hl hu)
  intro t ht
  have tp := (lt_min hl hu).trans_le ht.1
  have lg := Real.hasDerivAt_log tp.ne'
  have h := (((lg.pow 2).const_mul A).div_const 2).add
    ((((hasDerivAt_id t).mul lg).sub (hasDerivAt_id t)).const_mul B)
  convert h using 1 <;> try rfl
  all_goals try dsimp [primitive,piece]
  all_goals field_simp [tp.ne']; ring

def logMoment : ℝ := ((Real.log 2)^2-2*Real.log 2)/4

/-- The main and logarithmic moments of the unweighted band give the entire
prime-free dilation sum up to a uniform absolute error. -/
theorem log_band_error {x : ℝ} (large : 16 ≤ x) :
    |dilate ArithmeticFunction.log window x - (c*x*Real.log x+logMoment*x)| ≤ 73 := by
  have q := sum_integral_error large
  rw [piece_integral _ _ (by linarith) (by linarith),piece_integral _ _ (by linarith) (by linarith)] at q
  have log4 : Real.log 4 = 2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have eq : primitive (-x/2) 2 (x/2)-primitive (-x/2) 2 (x/4) +
      (primitive x (-1) x-primitive x (-1) (x/2)) = c*x*Real.log x+logMoment*x := by
    dsimp [primitive,c,logMoment]
    rw [Real.log_div (by linarith) (by norm_num),Real.log_div (by linarith) (by norm_num),log4]
    ring
  rwa [eq] at q

#print axioms log_band_error
end
end RiemannReduction.DivisorBand
