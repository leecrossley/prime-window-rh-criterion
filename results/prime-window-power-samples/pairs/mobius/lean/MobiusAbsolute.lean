import MobiusTail

open Finset ArithmeticFunction
namespace RiemannReduction.DivisorBand
noncomputable section

private lemma multiples_bound {a b q : ℕ} (hab : a ≤ b) (hq : 0 < q) :
    (((Ioc a b).filter (fun n => q ∣ n)).card : ℝ) ≤ ((b:ℝ)-a)/q+1 := by
  let s := (Ioc a b).filter (fun n => q ∣ n)
  have count : s.card ≤ (Ioc (a/q) (b/q)).card := by
    apply card_le_card_of_injOn (fun n => n/q)
    · intro n hn
      obtain ⟨bounds,dvd⟩ := mem_filter.mp hn
      obtain ⟨lo,hi⟩ := mem_Ioc.mp bounds
      exact mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hq).mpr ((Nat.div_mul_cancel dvd).symm ▸ lo),
        Nat.div_le_div_right hi⟩
    · intro x hx y hy eq
      simpa only [Nat.div_mul_cancel (mem_filter.mp hx).2,Nat.div_mul_cancel (mem_filter.mp hy).2]
        using congrArg (· * q) eq
  rw [Nat.card_Ioc] at count
  have countR : (s.card:ℝ) ≤ (b/q:ℕ) - (↑(a/q:ℕ):ℝ) := by
    rw [← Nat.cast_sub (Nat.div_le_div_right hab)]
    exact_mod_cast count
  have upper : (↑(b/q:ℕ):ℝ)*(q:ℝ) ≤ b := by exact_mod_cast Nat.div_mul_le_self b q
  have lower : (a:ℝ) < (↑(a/q:ℕ):ℝ)*q+q := by exact_mod_cast Nat.lt_div_mul_add (a := a) hq
  apply countR.trans
  rw [← sub_le_iff_le_add,le_div_iff₀ (Nat.cast_pos.mpr hq)]
  linarith

private lemma sum_inverse_squares (s k : ℕ) (hk : s+1 ≤ k) :
    ∑ p ∈ Ioc s k, 1/(p:ℝ)^2 ≤ 1/((s:ℝ)+1)^2+1/(s+1)-1/(k:ℝ) := by
  induction k, hk using Nat.le_induction with
  | base => rw [sum_Ioc_succ_top le_rfl]; simp
  | succ n hn ih =>
    rw [sum_Ioc_succ_top (by omega)]; push_cast
    have np : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    have step : 1/((n:ℝ)+1)^2 ≤ 1/n-1/(n+1) := by
      field_simp
      nlinarith
    linarith

/-- A crude lower bound for the odd squarefree integers in a short interval.
Exclude the even numbers and multiples of every square p² with p at least three. -/
theorem odd_squarefree_count {a b k : ℕ} (hab : a ≤ b) (cap : b ≤ k^2) (hk : 3 ≤ k) :
    ((b:ℝ)-a)/18-k-1 ≤ (((Ioc a b).filter (fun d => Odd d ∧ Squarefree d)).card:ℝ) := by
  let hits (p : ℕ) := (Ioc a b).filter (fun n => p^2 ∣ n)
  let evens := (Ioc a b).filter (fun n => 2 ∣ n)
  let bad := (Ioc a b).filter (fun n => ¬(Odd n ∧ Squarefree n))
  have cover : bad ⊆ evens ∪ (Ioc 2 k).biUnion hits := by
    intro n hn
    obtain ⟨mem,fail⟩ := mem_filter.mp hn
    by_cases dv : 2 ∣ n
    · exact mem_union_left _ (mem_filter.mpr ⟨mem,dv⟩)
    have odd : Odd n := Nat.not_even_iff_odd.mp (fun he => dv (even_iff_two_dvd.mp he))
    have ns : ¬ Squarefree n := fun sq => fail ⟨odd,sq⟩
    rw [Nat.squarefree_iff_prime_squarefree] at ns
    push Not at ns
    obtain ⟨p,prime,square⟩ := ns
    have div : p^2 ∣ n := by simpa [pow_two] using square
    have dne : p ≠ 2 := by rintro rfl; exact dv ((dvd_mul_right 2 2).trans square)
    obtain ⟨lo,hi⟩ := mem_Ioc.mp mem
    have pc := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
      ((Nat.le_of_dvd (by omega : 0 < n) div).trans (hi.trans cap))
    exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_Ioc.mpr ⟨by have := prime.two_le; omega,pc⟩,
      mem_filter.mpr ⟨mem,div⟩⟩)
  have badCount : bad.card ≤ evens.card + ∑ p ∈ Ioc 2 k, (hits p).card :=
    (card_le_card cover).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have countR : (bad.card:ℝ) ≤ (evens.card:ℝ)+∑ p ∈ Ioc 2 k, ((hits p).card:ℝ) := by exact_mod_cast badCount
  have ev : (evens.card:ℝ) ≤ ((b:ℝ)-a)/2+1 := by
    simpa only [Nat.cast_ofNat] using multiples_bound hab (by decide : 0 < 2)
  have oddCosts : (∑ p ∈ Ioc 2 k, ((hits p).card:ℝ)) ≤
      ∑ p ∈ Ioc 2 k, (((b:ℝ)-a)*(1/(p:ℝ)^2)+1) := by
    apply sum_le_sum
    intro p hp
    have pos : 0 < p^2 := pow_pos (by have := (mem_Ioc.mp hp).1; omega) _
    simpa only [Nat.cast_pow,div_eq_mul_inv,one_mul] using multiples_bound hab pos
  rw [sum_add_distrib,← mul_sum] at oddCosts
  have terms : ∑ _p ∈ Ioc 2 k, (1:ℝ) ≤ k := by simp
  have inv0 : 0 ≤ 1/(k:ℝ) := by positivity
  have decay : ∑ p ∈ Ioc 2 k, 1/(p:ℝ)^2 ≤ 4/9-1/(k:ℝ) := by
    convert sum_inverse_squares 2 k hk using 1
    norm_num
  have bound := mul_le_mul_of_nonneg_left (show ∑ p ∈ Ioc 2 k, 1/(p:ℝ)^2 ≤ 4/9 by linarith)
    (sub_nonneg.mpr (Nat.cast_le.mpr hab : (a:ℝ) ≤ b))
  have split := card_filter_add_card_filter_not (s := Ioc a b) (fun d => Odd d ∧ Squarefree d)
  rw [Nat.card_Ioc] at split
  have sr := congrArg (fun n : ℕ => (n:ℝ)) split
  simp only [Nat.cast_add,Nat.cast_sub hab] at sr
  change _ + (bad.card:ℝ) = _ at sr
  linarith

private lemma squarefree_count {a b k : ℕ} (hab : a ≤ b) (cap : b ≤ k^2) (hk : 2 ≤ k) :
    ((b:ℝ)-a)/4-k ≤ (((Ioc a b).filter Squarefree).card : ℝ) := by
  let hits (p : ℕ) := (Ioc a b).filter (fun n => p^2 ∣ n)
  have cover : (Ioc a b).filter (fun n => ¬ Squarefree n) ⊆ (Ioc 1 k).biUnion hits := by
    intro n hn
    obtain ⟨bounds,bad⟩ := mem_filter.mp hn
    obtain ⟨lo,hi⟩ := mem_Ioc.mp bounds
    rw [Nat.squarefree_iff_prime_squarefree] at bad
    push Not at bad
    obtain ⟨p,prime,dvd⟩ := bad
    have div : p^2 ∣ n := by simpa only [pow_two] using dvd
    have pc := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
      ((Nat.le_of_dvd (by omega : 0 < n) div).trans (hi.trans cap))
    exact mem_biUnion.mpr ⟨p,mem_Ioc.mpr ⟨prime.one_lt,pc⟩,mem_filter.mpr ⟨bounds,div⟩⟩
  have unionCount := (card_le_card cover).trans card_biUnion_le
  have bound : (((Ioc a b).filter (fun n => ¬ Squarefree n)).card:ℝ) ≤
      ∑ p ∈ Ioc 1 k, (((b:ℝ)-a)*(1/(p:ℝ)^2)+1) := by
    calc _ ≤ ∑ p ∈ Ioc 1 k, ((hits p).card:ℝ) := by exact_mod_cast unionCount
         _ ≤ _ := by
           apply sum_le_sum
           intro p hp
           have pp : 0 < p^2 := pow_pos (by have := (mem_Ioc.mp hp).1; omega) _
           simpa only [Nat.cast_pow,div_eq_mul_inv,one_mul] using multiples_bound hab pp
  rw [sum_add_distrib,← mul_sum] at bound
  have num : ∑ _p ∈ Ioc 1 k, (1:ℝ) ≤ k := by simp
  have inverse : ∑ p ∈ Ioc 1 k, 1/(p:ℝ)^2 ≤ 3/4-1/(k:ℝ) := by
    convert sum_inverse_squares 1 k hk using 1
    norm_num
  have inv0 : 0 ≤ 1/(k:ℝ) := by positivity
  have total := mul_le_mul_of_nonneg_left (show ∑ p ∈ Ioc 1 k, 1/(p:ℝ)^2 ≤ 3/4 by linarith)
    (sub_nonneg.mpr (Nat.cast_le.mpr hab : (a:ℝ) ≤ b))
  have split := card_filter_add_card_filter_not (s := Ioc a b) Squarefree
  rw [Nat.card_Ioc] at split
  have splitR := congrArg (fun n : ℕ => (n:ℝ)) split
  simp only [Nat.cast_add,Nat.cast_sub hab] at splitR
  linarith

/-- The residual is already bounded away from zero on part of its first unit interval. -/
theorem residual_first_bin {t : ℝ} (lo : 3/2 ≤ t) (hi : t < 2) :
    1/48 ≤ residual mainSlope t := by
  have floor1 : ⌊t⌋₊ = 1 := (Nat.floor_eq_iff (by linarith)).mpr ⟨by norm_num; linarith,by norm_num; linarith⟩
  have slope : mainSlope = c*(Real.eulerMascheroniConstant+1-c) := by
    unfold mainSlope c logMoment
    ring
  have cLo : 1/4 ≤ c := by unfold c; linarith [Real.log_two_gt_d9]
  have constant : Real.eulerMascheroniConstant+1-c ≤ 17/12 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have r : residual mainSlope t = c*t-mainSlope := by
    simp [residual,dilate,floor1,ArithmeticFunction.log_apply,harmonic]
  rw [r,slope]
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1/12 ≤ t-(Real.eulerMascheroniConstant+1-c))
    (by linarith : 0 ≤ c)]

/-- The triangle-inequality cost for the large divisors is at least quadratic in k. -/
theorem absolute_tail_lower {k : ℕ} (large : 100 ≤ k) :
    (k:ℝ)^2/2304 ≤ ∑ d ∈ Ioc k (k^2),
      |(ArithmeticFunction.moebius d:ℝ)*residual mainSlope ((k:ℝ)^2/d)| := by
  let a := k^2/2
  let b := 2*k^2/3
  let s := (Ioc a b).filter Squarefree
  have kk : k ≤ a := by
    dsimp [a]
    have : 2*k ≤ k^2 := by nlinarith
    omega
  have hab : a ≤ b := by dsimp [a,b]; omega
  have cap : b ≤ k^2 := by dsimp [b]; omega
  have wa : 2*(a:ℝ) ≤ (k:ℝ)^2 := by exact_mod_cast (show 2*a ≤ k^2 by dsimp [a]; omega)
  have wb : 2*(k:ℝ)^2 < 3*(b:ℝ)+3 := by exact_mod_cast (show 2*k^2 < 3*b+3 by dsimp [b]; omega)
  have many := squarefree_count hab cap (by omega : 2 ≤ k)
  have k100 : (100:ℝ) ≤ k := by exact_mod_cast large
  have m : (k:ℝ)^2/48 ≤ (s.card:ℝ) := by
    change _ ≤ (((Ioc a b).filter Squarefree).card:ℝ)
    nlinarith [mul_nonneg (show 0 ≤ (k:ℝ)-100 by linarith) (Nat.cast_nonneg (α := ℝ) k)]
  have subset : s ⊆ Ioc k (k^2) := fun d hd => by
    obtain ⟨lo,hi⟩ := mem_Ioc.mp (mem_filter.mp hd).1
    exact mem_Ioc.mpr ⟨kk.trans_lt lo,hi.trans cap⟩
  calc (k:ℝ)^2/2304 ≤ ∑ _d ∈ s, (1/48:ℝ) := by simp; linarith
       _ ≤ ∑ d ∈ s, |(ArithmeticFunction.moebius d:ℝ)*residual mainSlope ((k:ℝ)^2/d)| := by
         apply sum_le_sum
         intro d hd
         obtain ⟨bounds,sq⟩ := mem_filter.mp hd
         obtain ⟨left,right⟩ := mem_Ioc.mp bounds
         have dp : 0 < (d:ℝ) := Nat.cast_pos.mpr (by omega)
         have lower : 3*(d:ℝ) ≤ 2*(k:ℝ)^2 := by
           exact_mod_cast (show 3*d ≤ 2*k^2 by dsimp [b] at right; omega)
         have upper : (k:ℝ)^2 < 2*(d:ℝ) := by
           exact_mod_cast (show k^2 < 2*d by dsimp [a] at left; omega)
         have weight := residual_first_bin ((le_div_iff₀ dp).mpr (by linarith))
           ((div_lt_iff₀ dp).mpr upper)
         have absMu : |(ArithmeticFunction.moebius d:ℝ)| = 1 := by
           exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree sq
         rw [abs_mul,absMu,one_mul,abs_of_nonneg (by linarith : 0 ≤ residual mainSlope ((k:ℝ)^2/d))]
         exact weight
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => abs_nonneg _)

/-- Any set of m removed divisors can reduce the absolute mass by at most 100m. -/
theorem absolute_remaining_after_removal {k : ℕ} (large : 100 ≤ k) (S : Finset ℕ) :
    (k:ℝ)^2/2304-100*S.card ≤ ∑ d ∈ Ioc k (k^2) \ S, |tailTerm k d| := by
  let all := Ioc k (k^2)
  have subset : all ∩ S ⊆ all := inter_subset_left
  have each : (∑ d ∈ all ∩ S, |tailTerm k d|) ≤ ∑ _d ∈ all ∩ S, (100:ℝ) := by
    apply sum_le_sum
    intro d hd
    obtain ⟨lo,hi⟩ := mem_Ioc.mp (mem_inter.mp hd).1
    exact tailTerm_abs_le (by omega) hi
  have count : ((all ∩ S).card:ℝ) ≤ S.card := by exact_mod_cast card_le_card (show all ∩ S ⊆ S from inter_subset_right)
  simp only [sum_const,nsmul_eq_mul] at each
  have split := sum_sdiff (f := fun d => |tailTerm k d|) subset
  have rest : all \ (all ∩ S) = all \ S := by ext n; simp
  rw [rest] at split
  have mass : (k:ℝ)^2/2304 ≤ ∑ d ∈ all, |tailTerm k d| := absolute_tail_lower large
  change _ ≤ ∑ d ∈ all \ S, |tailTerm k d|
  linarith

#print axioms absolute_tail_lower
#print axioms absolute_remaining_after_removal
end
end RiemannReduction.DivisorBand
