import MobiusPrimeBalance

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius
namespace RiemannReduction.DivisorBand
noncomputable section

def hasLargePrime (k n : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n

def primesAboveRoot (k : ℕ) := (Icc 1 (k^2)).filter (fun p => p.Prime ∧ k < p)

private def primeIndicator (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun p => if p.Prime ∧ k < p then 1 else 0,by simp⟩

private lemma indicator_apply (k p : ℕ) :
    primeIndicator k p = (if p.Prime ∧ k<p then 1 else 0) := rfl

open Classical in
def smoothSum (k : ℕ) (A : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 (k^2) with ¬hasLargePrime k n, (moebius n:ℝ)*residual A ((k:ℝ)^2/n)

open Classical in
private lemma coefficient {k n : ℕ} (np : 0 < n) (cap : n ≤ k^2) :
    (primeIndicator k * (μ : ArithmeticFunction ℝ)) n =
      (if _ : hasLargePrime k n then -(moebius n:ℝ) else 0) := by
  classical
  simp only [mul_apply,intCoe_apply]
  rw [Nat.sum_divisorsAntidiagonal (fun p m => primeIndicator k p*(moebius m:ℝ))]
  by_cases h : hasLargePrime k n
  · rw [dif_pos h]
    obtain ⟨p,prime,pk,dvd⟩ := h
    let m := n/p
    have prod : p*m=n := Nat.mul_div_cancel' dvd
    have mp : 0 < m := Nat.div_pos (Nat.le_of_dvd np dvd) prime.pos
    have mk : m ≤ k := by
      by_contra! bad
      have compare := Nat.mul_le_mul (show k+1 ≤ p by omega) (show k+1 ≤ m by omega)
      nlinarith
    have only (q : ℕ) (qprime : q.Prime) (qk : k < q) (qdvd : q ∣ n) : q=p := by
      rw [← prod] at qdvd
      rcases qprime.dvd_mul.mp qdvd with d | d
      · exact (Nat.prime_dvd_prime_iff_eq qprime prime).mp d
      · have := Nat.le_of_dvd mp d; omega
    rw [sum_eq_single p]
    · have cop : p.Coprime m := prime.coprime_iff_not_dvd.mpr (fun d =>
        (not_le_of_gt (mk.trans_lt pk)) (Nat.le_of_dvd mp d))
      have sign := isMultiplicative_moebius.map_mul_of_coprime cop
      rw [prod,moebius_apply_prime prime,neg_one_mul] at sign
      simp [indicator_apply,prime,pk,sign,m]
    · intro q hq other
      have off : ¬(q.Prime ∧ k<q) := fun h => other (only q h.1 h.2 (Nat.mem_divisors.mp hq).1)
      simp [indicator_apply,off]
    · exact fun absent => (absent (Nat.mem_divisors.mpr ⟨dvd,np.ne'⟩)).elim
  · rw [dif_neg h]
    apply sum_eq_zero
    intro p hp
    have off : ¬(p.Prime ∧ k<p) := fun h' => h ⟨p,h'.1,h'.2,(Nat.mem_divisors.mp hp).1⟩
    simp [indicator_apply,off]

/-- Collect all multiples of each prime above the square root in a single term.
Every remaining divisor has all its prime factors at most k. -/
theorem large_prime_partition {k : ℕ} (hk : 0 < k) (A : ℝ) :
    D ((k:ℝ)^2) = A + smoothSum k A -
      ∑ p ∈ primesAboveRoot k, (D ((k:ℝ)^2/p)-A) := by
  classical
  let x := (k:ℝ)^2
  have floor : ⌊x⌋₊=k^2 := by dsimp [x]; rw [← Nat.cast_pow,Nat.floor_natCast]
  have x1 : 1 ≤ x := by
    dsimp [x]; exact_mod_cast (show 1 ≤ k^2 from Nat.pow_pos hk)
  have all := moebius_reconstruction A x1
  have conv := dilate_mul (primeIndicator k) (μ : ArithmeticFunction ℝ) (residual A) x
  have grouped : dilate (primeIndicator k) (dilate μ (residual A)) x =
      ∑ p ∈ primesAboveRoot k, (D (x/p)-A) := by
    unfold dilate primesAboveRoot
    rw [floor,sum_filter]
    apply sum_congr rfl
    intro p hp
    obtain ⟨pos,top⟩ := mem_Icc.mp hp
    by_cases good : p.Prime ∧ k<p
    · have px : (p:ℝ) ≤ x := by dsimp [x]; exact_mod_cast top
      have arg := (one_le_div (Nat.cast_pos.mpr pos)).mpr px
      have reconstruct := moebius_reconstruction A arg
      simp only [indicator_apply,if_pos good,one_mul]
      unfold dilate at reconstruct
      linarith
    · simp [indicator_apply,good]
  have smooth : dilate μ (residual A) x + dilate (primeIndicator k * (μ : ArithmeticFunction ℝ))
      (residual A) x = smoothSum k A := by
    unfold dilate smoothSum
    rw [floor,← sum_add_distrib,sum_filter]
    apply sum_congr rfl
    intro n hn
    obtain ⟨np,cap⟩ := mem_Icc.mp hn
    rw [coefficient np cap]
    by_cases h : hasLargePrime k n <;> simp [h,x,intCoe_apply]
  rw [conv,grouped] at smooth
  change D x=A+smoothSum k A-∑ p ∈ primesAboveRoot k, (D (x/p)-A)
  linarith

private lemma unit_packet {s : ℝ} (lo : 1 ≤ s) (hi : s < 2) :
    D s-mainSlope = residual mainSlope s := by
  have floor : ⌊s⌋₊ = 1 := (Nat.floor_eq_iff (by linarith)).mpr ⟨by norm_num; exact lo,by norm_num; exact hi⟩
  rw [moebius_reconstruction mainSlope lo]
  simp [dilate,floor,intCoe_apply]

lemma first_bin_at_square {k p : ℕ} (hk : 3 ≤ k) (hp : p ∈ binPrimes ((k:ℝ)^2)) :
    p ∈ primesAboveRoot k ∧ 1 ≤ (k:ℝ)^2/p ∧ (k:ℝ)^2/p < 2 := by
  let x := (k:ℝ)^2
  have kp : (3:ℝ) ≤ k := by exact_mod_cast hk
  have span : 2*(k:ℝ) ≤ x := by dsimp [x]; nlinarith
  have xpos : 0 ≤ x := sq_nonneg _
  obtain ⟨upper,lower⟩ := mem_sdiff.mp hp
  obtain ⟨cap,prime⟩ := Nat.mem_primesLE.mp upper
  have pp : (0:ℝ) < p := Nat.cast_pos.mpr prime.pos
  have up := (Nat.le_floor_iff (by positivity : 0 ≤ 2*x/3)).mp cap
  have low : x/2 < p := lt_of_not_ge (fun h => lower
    (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (by positivity)).mpr h,prime⟩))
  refine ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨prime.pos,?_⟩,prime,?_⟩,
    (one_le_div pp).mpr (by linarith),(div_lt_iff₀ pp).mpr (by linarith)⟩
  · exact_mod_cast (show (p:ℝ) ≤ (k:ℝ)^2 by change (p:ℝ) ≤ x; linarith)
  · exact_mod_cast (show (k:ℝ) < p by linarith)

/-- Grouping all multiples of each large prime still leaves an absolute sum
of at least order k²/log(k²). The sign between different groups matters. -/
theorem absolute_prime_groups_lower : ∀ᶠ k : ℕ in atTop,
    (k:ℝ)^2/(1280*Real.log ((k:ℝ)^2)) ≤
    ∑ p ∈ primesAboveRoot k, |D ((k:ℝ)^2/p)-mainSlope| := by
  filter_upwards [prime_bin_negative,eventually_ge_atTop (3:ℕ)] with k loss hk
  let x := (k:ℝ)^2
  calc x/(1280*Real.log x) ≤ -(∑ p ∈ binPrimes x, tailTerm k p) := by
           change ∑ p ∈ binPrimes x, tailTerm k p ≤ -x/(1280*Real.log x) at loss
           rw [neg_div] at loss
           simpa only [neg_neg] using neg_le_neg loss
       _ ≤ ∑ p ∈ binPrimes x, |D (x/p)-mainSlope| := by
           rw [← sum_neg_distrib]
           apply sum_le_sum
           intro p hp
           obtain ⟨isin,lo,hi⟩ := first_bin_at_square hk hp
           have prime := (mem_filter.mp isin).2.1
           change -((moebius p:ℝ)*residual mainSlope (x/p)) ≤ _
           rw [moebius_apply_prime prime,Int.cast_neg,Int.cast_one,neg_one_mul,neg_neg,unit_packet lo hi]
           exact le_abs_self _
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun p hp => (first_bin_at_square hk hp).1) (fun _ _ _ => abs_nonneg _)

private theorem bin_scale_superlinear (C : ℝ) : ∀ᶠ k : ℕ in atTop,
    C*k < (k:ℝ)^2/(1280*Real.log ((k:ℝ)^2)) := by
  let A := |C|+1
  have ap : 0 < A := by dsimp [A]; positivity
  have root := (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop (5120*A)
  filter_upwards [root,eventually_ge_atTop (3:ℕ)] with k large hk
  have k3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have kp : (0:ℝ) < k := by linarith
  have sq := Real.sq_sqrt kp.le
  have logpos := Real.log_pos (show 1 < (k:ℝ)^2 by nlinarith)
  have logs : Real.log ((k:ℝ)^2) ≤ 4*Real.sqrt k := by
    have lg := Real.log_le_rpow_div kp.le (show (0:ℝ)<1/2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at lg
    rw [Real.log_pow]; push_cast; linarith
  have top : A*(1280*Real.log ((k:ℝ)^2)) < (k:ℝ) := by
    change 5120*A < Real.sqrt k at large
    nlinarith [mul_le_mul_of_nonneg_left logs ap.le,mul_lt_mul_of_pos_right large (Real.sqrt_pos.mpr kp)]
  apply (lt_div_iff₀ (by positivity)).mpr
  have ca : C ≤ A := by dsimp [A]; linarith [le_abs_self C]
  have small := mul_le_mul_of_nonneg_right ca (show 0 ≤ 1280*Real.log ((k:ℝ)^2) by positivity)
  nlinarith [mul_lt_mul_of_pos_right (small.trans_lt top) kp]

/-- Even after all multiples of each large prime have been combined, their
absolute contributions eventually exceed every fixed allowance per root. -/
theorem absolute_prime_groups_superlinear (C : ℝ) : ∀ᶠ k : ℕ in atTop,
    C*k < ∑ p ∈ primesAboveRoot k, |D ((k:ℝ)^2/p)-mainSlope| := by
  filter_upwards [bin_scale_superlinear C,absolute_prime_groups_lower] with k lo hi
  exact lo.trans_le hi

theorem first_bin_count_superlinear (C : ℝ) : ∀ᶠ k : ℕ in atTop,
    C*k < ((binPrimes ((k:ℝ)^2)).card:ℝ) := by
  filter_upwards [bin_scale_superlinear (100*C),prime_bin_negative,eventually_ge_atTop (3:ℕ)] with k growth loss hk
  let S := binPrimes ((k:ℝ)^2)
  have sub : S ⊆ primesAboveRoot k := fun p hp => (first_bin_at_square hk hp).1
  have low : ∑ _p ∈ S, (-100:ℝ) ≤ ∑ p ∈ S, tailTerm k p := by
    apply sum_le_sum
    intro p hp
    have inRange := mem_Icc.mp (mem_filter.mp (sub hp)).1
    exact (abs_le.mp (tailTerm_abs_le inRange.1 inRange.2)).1
  simp only [sum_const,nsmul_eq_mul] at low
  change ∑ p ∈ S, tailTerm k p ≤ _ at loss
  change C*k < (S.card:ℝ)
  rw [neg_div] at loss
  linarith

#print axioms absolute_prime_groups_superlinear
#print axioms large_prime_partition
#print axioms absolute_prime_groups_lower
end
end RiemannReduction.DivisorBand
