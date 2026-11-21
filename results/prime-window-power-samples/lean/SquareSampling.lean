import PositivePole
import PrimeBandWeights

open Lean Elab Command in
run_cmd do
  for name in [`riemannHypothesis, `rhOfAll, `allChi,
      `UpperTheory.FinalTheorems.riemannHypothesis, `UpperTheory.FinalTheorems.everyCharacter,
      `RiemannReduction.rh_of_right, `RiemannReduction.PrimeGrid.rh_of_fifth_blocks,
      `RiemannReduction.PrimeGrid.rh_of_integer_product_blocks] do
    if (← getEnv).contains name then
      throwError "Unexpected imported declaration {name}"

open Finset Filter
open scoped ArithmeticFunction.vonMangoldt
namespace RiemannReduction.PrimeGrid
noncomputable section

private def d (x : ℝ) := x/2*Real.log 2 - ThetaTransfer.primePowerSum (x/4)
private def knot (x : ℝ) (k : ℕ) := max (x-k) 0
private def excess (a b : ℕ) (x t : ℝ) (k : ℕ) :=
  (1-t)*knot a k + t*knot b k - knot x k
private def coeff (n : ℕ) : ℝ := Λ n / (2*n)

private lemma common_sum {x : ℝ} {b : ℕ} (hx : 0 ≤ x) (cap : x ≤ b) :
    ThetaTransfer.primePowerSum (x/4) = ∑ n ∈ range (b+1), Λ n*weight x n := by
  rw [ThetaTransfer.primePowerSum,show 4*(x/4) = x by ring]
  calc _ = ∑ n ∈ range (⌊x⌋₊+1), Λ n*weight x n := by
         apply sum_congr rfl
         intro n _
         rcases Nat.eq_zero_or_pos n with rfl | pos
         · simp
         · rw [weight_eq_tent _ pos]
       _ = _ := by
         have floorCap : ⌊x⌋₊ ≤ b := Nat.cast_le.mp ((Nat.floor_le hx).trans cap)
         apply sum_subset (range_subset_range.mpr (by omega))
         intro n _ off
         simp only [mem_range,not_lt] at off
         have above : (⌊x⌋₊:ℝ)+1 ≤ n := by exact_mod_cast off
         simp [weight_zero_before ((Nat.lt_floor_add_one x).trans_le above).le]

private lemma excess_nonneg {a b : ℕ} {x t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (mix : x = (1-t)*a+t*b) (k : ℕ) : 0 ≤ excess a b x t k := by
  unfold excess knot
  apply sub_nonneg.mpr
  apply max_le
  · calc x-k = (1-t)*((a:ℝ)-k)+t*((b:ℝ)-k) := by rw [mix]; ring
         _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
           (mul_le_mul_of_nonneg_left (le_max_left _ _) ht)
  · exact add_nonneg (mul_nonneg (by linarith) (le_max_right _ _)) (mul_nonneg ht (le_max_right _ _))

private lemma excess_off {a b k : ℕ} {x t : ℝ} (ax : (a:ℝ) ≤ x) (xb : x ≤ b)
    (mix : x = (1-t)*a+t*b) (off : k ∉ Icc a b) : excess a b x t k = 0 := by
  have ab : a ≤ b := Nat.cast_le.mp (ax.trans xb)
  rcases lt_or_ge k a with left | right
  · have ka : (k:ℝ) ≤ a := Nat.cast_le.mpr left.le
    simp only [excess,knot,max_eq_left (sub_nonneg.mpr ka),
      max_eq_left (sub_nonneg.mpr (ka.trans ax)),max_eq_left (sub_nonneg.mpr (ka.trans (ax.trans xb)))]
    rw [mix]
    ring
  · have bk : (b:ℝ) ≤ k := Nat.cast_le.mpr (show b ≤ k by
        by_contra! h; exact off (mem_Icc.mpr ⟨right,h.le⟩))
    simp [excess,knot,max_eq_right (sub_nonpos.mpr bk),max_eq_right (sub_nonpos.mpr (xb.trans bk)),
      max_eq_right (sub_nonpos.mpr (ax.trans (xb.trans bk)))]

private lemma error_class {a b c : ℕ} {x t : ℝ} (pa : 0 < a) (ax : (a:ℝ) ≤ x) (xb : x ≤ b)
    (ht : t ≤ 1) (mix : x = (1-t)*a+t*b) (hc : 0 < c) (small : c ≤ 4) :
    ∑ n ∈ range (b+1), coeff n * excess a b x t (c*n) ≤
      (↑(b-a+1 : ℕ):ℝ) * (2*Real.log b/a * ((b:ℝ)-a)) := by
  let S := (range (b+1)).filter (fun n => c*n ∈ Icc a b)
  have ab : a ≤ b := Nat.cast_le.mp (ax.trans xb)
  have aPos : 0 < (a:ℝ) := Nat.cast_pos.mpr pa
  have width : 0 ≤ (b:ℝ)-a := sub_nonneg.mpr (ax.trans xb)
  have logPos := Real.log_natCast_nonneg b
  have count : S.card ≤ b-a+1 := by
    have le := Finset.card_le_card_of_injOn (s := S) (t := Icc a b) (fun n => c*n)
      (fun n hn => (mem_filter.mp hn).2) (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hc h)
    rw [Nat.card_Icc] at le
    omega
  have restrict : ∑ n ∈ S, coeff n * excess a b x t (c*n) =
      ∑ n ∈ range (b+1), coeff n * excess a b x t (c*n) := by
    apply sum_subset (filter_subset _ _)
    intro n hn no
    simp [excess_off ax xb mix (fun hit => no (mem_filter.mpr ⟨hn,hit⟩))]
  rw [← restrict]
  calc _ ≤ ∑ _n ∈ S, (2*Real.log b/a)*((b:ℝ)-a) := by
         apply sum_le_sum
         intro n hn
         obtain ⟨inRange,loc⟩ := mem_filter.mp hn
         obtain ⟨left,right⟩ := mem_Icc.mp loc
         have np : 0 < n := by
           by_contra! z
           have zero : n = 0 := by omega
           have : a ≤ 0 := by simpa only [zero,mul_zero] using left
           omega
         have nPos : 0 < (n:ℝ) := Nat.cast_pos.mpr np
         have nle : n ≤ b := by have := mem_range.mp inRange; omega
         have size : (a:ℝ) ≤ 4*n := by exact_mod_cast left.trans (Nat.mul_le_mul_right n small)
         have cBound : coeff n ≤ 2*Real.log b/a := by
           apply (div_le_div_iff₀ (by positivity : 0 < 2*(n:ℝ)) aPos).mpr
           have logN := ArithmeticFunction.vonMangoldt_le_log (n := n)
           have v := logN.trans (Real.log_le_log nPos (Nat.cast_le.mpr nle))
           nlinarith [mul_le_mul_of_nonneg_right v aPos.le,mul_le_mul_of_nonneg_left size logPos]
         have kl : (a:ℝ) ≤ ↑(c*n:ℕ) := Nat.cast_le.mpr left
         have kr : (↑(c*n:ℕ):ℝ) ≤ b := Nat.cast_le.mpr right
         have error : excess a b x t (c*n) ≤ (b:ℝ)-a := by
           simp only [excess,knot,max_eq_right (sub_nonpos.mpr kl),mul_zero,zero_add,
             max_eq_left (sub_nonneg.mpr kr)]
           linarith [mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr kr),le_max_right (x-↑(c*n:ℕ)) (0:ℝ)]
         exact (mul_le_mul_of_nonneg_left error (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))).trans
           (mul_le_mul_of_nonneg_right cBound width)
       _ = (S.card:ℝ)*_ := by simp
       _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast count) (by positivity)

private lemma chord_bounds {a b : ℕ} {x t : ℝ} (pa : 0 < a) (ax : (a:ℝ) ≤ x) (xb : x ≤ b)
    (ht : 0 ≤ t) (ht' : t ≤ 1) (mix : x = (1-t)*a+t*b) :
    min (powerMargin a) (powerMargin b) - 6*(↑(b-a+1 : ℕ):ℝ)*((b:ℝ)-a)*Real.log b/a ≤ d x ∧
    d x ≤ max (powerMargin a) (powerMargin b) +
      6*(↑(b-a+1 : ℕ):ℝ)*((b:ℝ)-a)*Real.log b/a := by
  let F (u : ℝ) := ∑ n ∈ range (b+1), Λ n*weight u n
  let e := excess a b x t
  have changeSum : (1-t)*F a + t*F b - F x =
      ∑ n ∈ range (b+1), coeff n*(2*e n - 3*e (2*n) + e (4*n)) := by
    unfold F
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    change (1-t)*(Λ n*((2*knot a n-3*knot a (2*n)+knot a (4*n))/(2*n))) +
      t*(Λ n*((2*knot b n-3*knot b (2*n)+knot b (4*n))/(2*n))) -
      Λ n*((2*knot x n-3*knot x (2*n)+knot x (4*n))/(2*n)) = _
    unfold e excess coeff
    ring
  have err : (1-t)*F a + t*F b - F x ≤
      2*(∑ n ∈ range (b+1),coeff n*e n) + ∑ n ∈ range (b+1),coeff n*e (4*n) := by
    rw [changeSum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply sum_le_sum
    intro n _
    have positive : 0 ≤ coeff n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    nlinarith [mul_nonneg positive (show 0 ≤ e (2*n) from excess_nonneg ht ht' mix _)]
  have below : -(3*(∑ n ∈ range (b+1),coeff n*e (2*n))) ≤ (1-t)*F a+t*F b-F x := by
    rw [changeSum,Finset.mul_sum,← Finset.sum_neg_distrib]
    apply sum_le_sum
    intro n _
    have positive : 0 ≤ coeff n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    nlinarith [mul_nonneg positive (show 0 ≤ e n from excess_nonneg ht ht' mix _),
      mul_nonneg positive (show 0 ≤ e (4*n) from excess_nonneg ht ht' mix _)]
  have first := error_class (c := 1) pa ax xb ht' mix (by decide) (by decide)
  simp only [one_mul] at first
  have last := error_class (c := 4) pa ax xb ht' mix (by decide) (by decide)
  have middle := error_class (c := 2) pa ax xb ht' mix (by decide) (by decide)
  have bound : (1-t)*F a+t*F b-F x ≤ 6*(↑(b-a+1:ℕ):ℝ)*((b:ℝ)-a)*Real.log b/a := by
    dsimp only [e] at err
    linear_combination err + 2*first + last
  have lower : -(6*(↑(b-a+1:ℕ):ℝ)*((b:ℝ)-a)*Real.log b/a) ≤ (1-t)*F a+t*F b-F x := by
    dsimp only [e] at below
    linear_combination below + 3*middle
  have A : powerMargin a = (a:ℝ)/2*Real.log 2-F a := by
    rw [powerMargin, common_sum (Nat.cast_nonneg a) (ax.trans xb)]
  have B : powerMargin b = (b:ℝ)/2*Real.log 2-F b := by
    rw [powerMargin, common_sum (Nat.cast_nonneg b) (le_refl (b:ℝ))]
  have X : d x = x/2*Real.log 2-F x := by rw [d,common_sum ((Nat.cast_nonneg _).trans ax) xb]
  rw [X]
  have avg : (1-t)*powerMargin a+t*powerMargin b ≤ max (powerMargin a) (powerMargin b) := by
    calc _ ≤ (1-t)*max (powerMargin a) (powerMargin b)+t*max (powerMargin a) (powerMargin b) :=
             add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht'))
               (mul_le_mul_of_nonneg_left (le_max_right _ _) ht)
         _ = _ := by ring
  have avgLo : min (powerMargin a) (powerMargin b) ≤ (1-t)*powerMargin a+t*powerMargin b := by
    calc _ = (1-t)*min (powerMargin a) (powerMargin b)+t*min (powerMargin a) (powerMargin b) := by ring
         _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) (sub_nonneg.mpr ht'))
             (mul_le_mul_of_nonneg_left (min_le_right _ _) ht)
  have eq : x/2*Real.log 2-F x =
      (1-t)*powerMargin a+t*powerMargin b + ((1-t)*F a+t*F b-F x) := by
    rw [A,B,mix]
    ring
  rw [eq]
  exact ⟨by linarith [add_le_add avgLo lower],add_le_add avg bound⟩

/-- Between two consecutive squares the margin stays within a logarithmic error
of the interval between its two endpoint values. -/
private lemma between_squares {n : ℕ} (hn : 0 < n) {x : ℝ}
    (ax : (↑(n^2 : ℕ):ℝ) ≤ x) (xb : x ≤ ↑((n+1)^2 : ℕ)) :
    min (powerMargin (n^2)) (powerMargin ((n+1)^2)) -
      72*Real.log (↑((n+1)^2 : ℕ):ℝ) ≤ d x ∧
    d x ≤ max (powerMargin (n^2)) (powerMargin ((n+1)^2)) +
      72*Real.log (↑((n+1)^2 : ℕ):ℝ) := by
  let a := n^2
  let b := (n+1)^2
  have width : b = a+(2*n+1) := by dsimp [a,b]; ring
  have subN : b-a = 2*n+1 := by omega
  have aPos : 0 < a := pow_pos hn _
  have diff : (b:ℝ)-a = 2*n+1 := by rw [width]; push_cast; ring
  have diffPos : 0 < (b:ℝ)-a := by rw [diff]; positivity
  let t := (x-a)/((b:ℝ)-a)
  have t0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr ax) diffPos.le
  have t1 : t ≤ 1 := (div_le_one diffPos).mpr (sub_le_sub_right xb _)
  have mix : x = (1-t)*a+t*b := by
    dsimp [t]
    field_simp [diffPos.ne']
    ring
  have h := chord_bounds (a := a) (b := b) aPos ax xb t0 t1 mix
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have product : (2*(n:ℝ)+2)*(2*n+1) ≤ (4*n)*(3*n) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have normalized : 6*(↑(b-a+1 : ℕ):ℝ)*((b:ℝ)-a)/a ≤ 72 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr aPos : 0 < (a:ℝ))).mpr
    rw [subN,diff]
    dsimp [a]
    push_cast
    linarith
  have err : 6*(↑(b-a+1 : ℕ):ℝ)*((b:ℝ)-a)*Real.log b/a ≤ 72*Real.log b := calc
    _ = (6*(↑(b-a+1 : ℕ):ℝ)*((b:ℝ)-a)/a)*Real.log b := by ring
    _ ≤ 72*Real.log b := mul_le_mul_of_nonneg_right normalized (Real.log_natCast_nonneg b)
  exact ⟨(sub_le_sub_left err _).trans h.1,h.2.trans (add_le_add le_rfl err)⟩

private lemma small_log {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, 72*Real.log (4*x) ≤ (c/8)*Real.sqrt x := by
  have l := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).bound
    (show 0 < c/1152 by positivity)
  filter_upwards [l,eventually_ge_atTop (4:ℝ)] with x h hx
  have xp : 0 < x := by linarith
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (show 1 ≤ x by linarith)),
    ← Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg _)] at h
  rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) xp.ne']
  linarith [Real.log_le_log (by norm_num : (0:ℝ)<4) hx]

/-- Every positive allowance is met at arbitrarily large perfect squares, without RH. -/
theorem cofinal_square_endpoints {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ N ≥ m, -c*(N:ℝ) < powerMargin (N^2) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (small_log hc)
  obtain ⟨A,hit⟩ := prime_power_recovers (c := c/8) (by positivity) (δ := 1) (by norm_num)
  let B := max (max T 4) (((m:ℝ)+2)^2)
  have four : 4 ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have posB : 0 < B := by linarith
  obtain ⟨u,hu,high⟩ := hit (max A (Real.log B)) (le_max_left _ _)
  let x := Real.exp u
  have big : B ≤ x := (Real.log_le_iff_le_exp posB).mp ((le_max_right _ _).trans hu.1)
  have big4 := four.trans big
  have xp : 0 ≤ x := (Real.exp_pos u).le
  have sx := Real.sq_sqrt xp
  have root2 : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith)
  let n := ⌊Real.sqrt x⌋₊
  have left : (n:ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg _)
  have right : Real.sqrt x < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have n1 : 1 ≤ n := (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (by push_cast; linarith)
  have npos : 0 < n := by omega
  have near : Real.sqrt x ≤ 2*(n:ℝ) := by
    have h : (1:ℝ) ≤ n := by exact_mod_cast n1
    linarith
  have rootM := Real.le_sqrt_of_sq_le ((le_max_right (max T 4) (((m:ℝ)+2)^2)).trans big)
  have mn : m ≤ n := (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (by linarith)
  have ax : (↑(n^2 : ℕ):ℝ) ≤ x := by
    push_cast
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) left 2).trans_eq sx
  have xb : x ≤ (↑((n+1)^2 : ℕ):ℝ) := by
    push_cast
    exact sx.symm.trans_le (pow_le_pow_left₀ (Real.sqrt_nonneg _) right.le 2)
  have cap : (↑((n+1)^2 : ℕ):ℝ) ≤ 4*x := by
    push_cast
    have p := pow_le_pow_left₀ (show 0 ≤ (n:ℝ)+1 by positivity)
      (show (n:ℝ)+1 ≤ 2*Real.sqrt x by linarith) 2
    nlinarith
  have logs := hT x (((le_max_left T 4).trans (le_max_left _ _)).trans big)
  have l := Real.log_le_log (by positivity : (0:ℝ) < ↑((n+1)^2 : ℕ)) cap
  have sqrt : Real.sqrt x = Real.exp (u/2) := by
    dsimp [x]; rw [Real.sqrt_eq_rpow,← Real.exp_mul]; congr 1; ring
  have recovery : -(c/8)*Real.sqrt x < d x := by
    rw [sqrt]
    unfold d
    unfold ThetaTransfer.primePowerDeficit at high
    dsimp only [x]
    linarith
  by_contra! no
  have a := no n mn
  have b := no (n+1) (by omega)
  push_cast at b
  have ceiling : max (powerMargin (n^2)) (powerMargin ((n+1)^2)) ≤ -c*(n:ℝ) :=
    max_le a (by linarith)
  have chord := (between_squares npos ax xb).2
  nlinarith [mul_le_mul_of_nonneg_left near hc.le,
    mul_pos hc (Real.sqrt_pos.mpr (Real.exp_pos u))]

/-- In particular the requested upper endpoint satisfies the one-fifth bound for unbounded N. -/
theorem cofinal_fifth_square_endpoints (m : ℕ) :
    ∃ N ≥ m, -(Real.sqrt (N*N : ℕ)/5) < powerMargin (N*N) := by
  obtain ⟨N,hm,h⟩ := cofinal_square_endpoints (c := 1/5) (by norm_num) m
  refine ⟨N,hm,?_⟩
  rw [← pow_two, Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg N)]
  linarith

/-- Taking a good square as the start of a block also gives arbitrarily large lower endpoints. -/
theorem cofinal_fifth_lower_endpoints (m : ℕ) :
    ∃ N ≥ m, -(Real.sqrt N/5) < powerMargin N := by
  obtain ⟨n,hm,h⟩ := cofinal_fifth_square_endpoints m
  have size : n ≤ n*n := (Nat.le_self_pow (by decide : 2 ≠ 0) n).trans_eq (pow_two n)
  exact ⟨n*n,hm.trans size,h⟩

/-- A uniform bound with a little slack at the squares alone would control every integer
on a square block. The sampled root interval is [K,K²] and the resulting block is [K²,K⁴]. -/
theorem whole_sqrt_blocks_of_square_samples {C ε : ℝ} (hc : 0 ≤ C) (he : 0 < ε)
    (samples : ∀ m : ℕ, ∃ K ≥ m, ∀ k ∈ Icc K (K*K), -C*k ≤ powerMargin (k^2)) :
    ∀ m : ℕ, ∃ N ≥ m, ∀ j : ℕ, j ∈ Icc N (N*N) → -(C+ε)*Real.sqrt j ≤ powerMargin j := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (small_log (c := 4*ε) (by positivity))
  intro m
  let cutoff := max (max m 1) ⌈2*C/ε⌉₊
  obtain ⟨K,hK,check⟩ := samples (max cutoff ⌈T⌉₊)
  have early : cutoff ≤ K := (le_max_left _ _).trans hK
  have base : max m 1 ≤ K := (le_max_left _ _).trans early
  let N := K*K
  have KN : K ≤ N := (Nat.le_self_pow (by decide : 2 ≠ 0) K).trans_eq (pow_two K)
  refine ⟨N,((le_max_left m 1).trans base).trans KN,fun j hj => ?_⟩
  obtain ⟨lo,hi⟩ := mem_Icc.mp hj
  by_cases last : j = N*N
  · have hv := check N (mem_Icc.mpr ⟨KN,le_rfl⟩)
    rw [last,← pow_two,Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg N)]
    nlinarith [mul_nonneg he.le (Nat.cast_nonneg (α := ℝ) N)]
  let n := j.sqrt
  have start : K ≤ n := Nat.le_sqrt.mpr lo
  have stop : n+1 ≤ N := by
    by_contra! h
    have ns : N ≤ j.sqrt := by omega
    exact last (le_antisymm hi (Nat.le_sqrt.mp ns))
  have v1 := check n (mem_Icc.mpr ⟨start,by omega⟩)
  have v2 := check (n+1) (mem_Icc.mpr ⟨by omega,stop⟩)
  have nn : (n:ℝ) ≤ Real.sqrt j := Real.nat_sqrt_le_real_sqrt
  have one : (1:ℝ) ≤ n := by exact_mod_cast ((le_max_right m 1).trans base).trans start
  have big : (1:ℝ) ≤ Real.sqrt j := one.trans nn
  have slack : 2*C ≤ Real.sqrt j*ε := (div_le_iff₀ he).mp ((Nat.le_ceil _).trans
    ((Nat.cast_le.mpr (((le_max_right _ _).trans early).trans start)).trans nn))
  have pos : 0 < n := by omega
  have ax : (↑(n^2 : ℕ):ℝ) ≤ j := Nat.cast_le.mpr (Nat.sqrt_le' j)
  have xb : (j:ℝ) ≤ ↑((n+1)^2 : ℕ) := Nat.cast_le.mpr (Nat.lt_succ_sqrt' j).le
  have upper : (↑((n+1)^2 : ℕ):ℝ) ≤ 4*j := by
    push_cast
    have h := pow_le_pow_left₀ (show 0 ≤ (n:ℝ)+1 by positivity)
      (show (n:ℝ)+1 ≤ 2*Real.sqrt j by linarith) 2
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg j)]
  have fromT : T ≤ (j:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr
    (((le_max_right cutoff _).trans hK).trans (KN.trans lo)))
  have logs := hT (j:ℝ) fromT
  have comp := Real.log_le_log (by positivity : (0:ℝ) < ↑((n+1)^2 : ℕ)) upper
  have chord := (between_squares pos ax xb).1
  have low : -C*(Real.sqrt j+1) ≤ min (powerMargin (n^2)) (powerMargin ((n+1)^2)) := by
    push_cast at v2
    have order := mul_le_mul_of_nonneg_left nn hc
    exact le_min (by linarith) (by linarith)
  change _ ≤ d j
  nlinarith

theorem whole_fifth_blocks_of_square_samples
    (samples : ∀ m : ℕ, ∃ K ≥ m, ∀ k ∈ Icc K (K*K), -(39/200:ℝ)*k ≤ powerMargin (k^2)) :
    ∀ m : ℕ, ∃ N ≥ m, ∀ j : ℕ, j ∈ Icc N (N*N) → -(Real.sqrt j/5) ≤ powerMargin j := by
  intro m
  obtain ⟨N,hm,checks⟩ := whole_sqrt_blocks_of_square_samples (C := 39/200) (ε := 1/200)
    (by norm_num) (by norm_num) samples m
  exact ⟨N,hm,fun j hj => by linarith [checks j hj]⟩

#print axioms cofinal_square_endpoints
#print axioms cofinal_fifth_square_endpoints
#print axioms cofinal_fifth_lower_endpoints
#print axioms whole_sqrt_blocks_of_square_samples
#print axioms whole_fifth_blocks_of_square_samples
end
end RiemannReduction.PrimeGrid
