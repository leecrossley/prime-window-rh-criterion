import PrimeGrid

open Finset
namespace RiemannReduction.PrimeGrid

private noncomputable def kink (j k : ℕ) : ℝ := max ((j:ℝ)-k) 0
private def active (n k : ℕ) : ℝ := if k ≤ n then 1 else 0
private noncomputable def remainder (n j k : ℕ) : ℝ :=
  if k ≤ n then max ((k:ℝ)-j) 0 else kink j k

private lemma kink_expand (j n k : ℕ) :
    kink j k = kink n k + active n k*((j:ℝ)-n) + remainder n j k := by
  by_cases center : k ≤ n
  · have kn := Nat.cast_le (α := ℝ).mpr center
    simp only [kink, active, remainder, if_pos center, max_eq_left (sub_nonneg.mpr kn), one_mul]
    rcases le_total (k:ℝ) j with h | h <;>
      simp only [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)] <;> ring
  · simp [kink, active, remainder, center, max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr (le_of_not_ge center) : (n:ℝ) ≤ k))]

private lemma remainder_nonneg (n j k : ℕ) : 0 ≤ remainder n j k := by
  unfold remainder kink
  split <;> exact le_max_right _ _

private lemma remainder_le {n j h : ℕ} (hj : j ∈ Icc (n-h) (n+h)) (k : ℕ) :
    remainder n j k ≤ h := by
  obtain ⟨lo,hi⟩ := mem_Icc.mp hj
  unfold remainder kink
  split_ifs with hk
  · apply max_le _ (Nat.cast_nonneg _)
    exact sub_le_iff_le_add.mpr (by exact_mod_cast (show k ≤ h+j by omega))
  · apply max_le _ (Nat.cast_nonneg _)
    exact sub_le_iff_le_add.mpr (by exact_mod_cast (show j ≤ h+k by omega))

private lemma remainder_off {n j k h : ℕ} (hj : j ∈ Icc (n-h) (n+h)) (hk : k ∉ Icc (n-h) (n+h)) :
    remainder n j k = 0 := by
  obtain ⟨lo,hi⟩ := mem_Icc.mp hj
  by_cases kn : k ≤ n
  · have lt : k < n-h := by
      by_contra! bad
      exact hk (mem_Icc.mpr ⟨bad, by omega⟩)
    simp [remainder, kn, max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr (lt.le.trans lo) : (k:ℝ) ≤ j))]
  · have lt : n+h < k := by
      by_contra! bad
      exact hk (mem_Icc.mpr ⟨by omega,bad⟩)
    simp [remainder, kn, kink, max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr (hi.trans lt.le) : (j:ℝ) ≤ k))]

private noncomputable def coefficient (p : ℕ) : ℝ := Real.log p/(2*p)
private noncomputable def localSlope (n p : ℕ) : ℝ :=
  coefficient p * (2*active n p-3*active n (2*p)+active n (4*p))
private noncomputable def localError (n j p : ℕ) : ℝ :=
  coefficient p * (2*remainder n j p-3*remainder n j (2*p)+remainder n j (4*p))

private lemma expand_weight (n j p : ℕ) :
    Real.log p*weight j p = Real.log p*weight n p + localSlope n p*((j:ℝ)-n) + localError n j p := by
  change Real.log p*((2*kink j p-3*kink j (2*p)+kink j (4*p))/(2*p)) =
    Real.log p*((2*kink n p-3*kink n (2*p)+kink n (4*p))/(2*p)) + _ + _
  rw [kink_expand j n p, kink_expand j n (2*p), kink_expand j n (4*p)]
  unfold localSlope localError coefficient
  ring

private noncomputable def slope (n h : ℕ) : ℝ := Real.log 2/2 - ∑ p ∈ primes (n+h), localSlope n p

private lemma expand_margin {n h j : ℕ} (hj : j ∈ Icc (n-h) (n+h)) :
    margin j = margin n + slope n h*((j:ℝ)-n) - ∑ p ∈ primes (n+h), localError n j p := by
  have common (i : ℕ) (hi : i ≤ n+h) : margin i = (i:ℝ)/2*Real.log 2 - sumTo (n+h) i := by
    rw [margin, Nat.floor_natCast, sumTo_extend hi (by linarith : (i:ℝ)<(i:ℝ)+1)]
  have e : sumTo (n+h) j = sumTo (n+h) n + (∑ p ∈ primes (n+h), localSlope n p)*((j:ℝ)-n) +
      ∑ p ∈ primes (n+h), localError n j p := by
    simp only [sumTo, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => expand_weight n j p
  rw [common j (mem_Icc.mp hj).2, common n (by omega), e, slope]
  ring

private lemma one_kink_sum {n h j c : ℕ} (hn : 0 < n) (hh : 2*h ≤ n) (hj : j ∈ Icc (n-h) (n+h))
    (hc : 0 < c) (hc4 : c ≤ 4) :
    ∑ p ∈ primes (n+h), coefficient p*remainder n j (c*p) ≤
      (2*(h:ℝ)+1)*(4*h*Real.log (2*n)/n) := by
  let S := (primes (n+h)).filter fun p => c*p ∈ Icc (n-h) (n+h)
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hl : 0 ≤ Real.log (2*n) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*n by omega))
  have count : S.card ≤ 2*h+1 := by
    have sub : S.card ≤ (Icc (n-h) (n+h)).card :=
      Finset.card_le_card_of_injOn (fun p => c*p) (fun p hp => (mem_filter.mp hp).2)
        (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hc he)
    rw [Nat.card_Icc] at sub
    omega
  have restrict : ∑ p ∈ S, coefficient p*remainder n j (c*p) =
      ∑ p ∈ primes (n+h), coefficient p*remainder n j (c*p) := by
    apply Finset.sum_subset (filter_subset _ _)
    intro p hp notMem
    have off : c*p ∉ Icc (n-h) (n+h) := fun hit => notMem (mem_filter.mpr ⟨hp,hit⟩)
    simp [remainder_off hj off]
  rw [← restrict]
  calc _ ≤ ∑ _p ∈ S, 4*(h:ℝ)*Real.log (2*n)/n := by
         apply Finset.sum_le_sum
         intro p hp
         obtain ⟨hp, loc⟩ := mem_filter.mp hp
         obtain ⟨inside, _⟩ := mem_Icc.mp loc
         obtain ⟨upper,pr⟩ := Nat.mem_primesLE.mp hp
         have pp : 0 < (p:ℝ) := Nat.cast_pos.mpr pr.pos
         have size : n ≤ 8*p := by have := Nat.mul_le_mul_right p hc4; omega
         have hlog : Real.log p ≤ Real.log (2*n) :=
           Real.log_le_log pp (by exact_mod_cast (show p ≤ 2*n by omega))
         have cw : coefficient p ≤ 4*Real.log (2*n)/n := by
           apply (div_le_div_iff₀ (by positivity : 0 < 2*(p:ℝ)) hn').mpr
           have a := mul_le_mul_of_nonneg_right hlog hn'.le
           have z : (n:ℝ) ≤ 8*p := by exact_mod_cast size
           nlinarith [mul_le_mul_of_nonneg_left z hl]
         calc _ ≤ (4*Real.log (2*n)/n)*h := mul_le_mul cw (remainder_le hj _) (remainder_nonneg ..) (by positivity)
              _ = _ := by ring
       _ = (S.card:ℝ)*(4*h*Real.log (2*n)/n) := by simp
       _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast count) (by positivity)

/-- A slope through the center approximates the margin from below on the entire interval.
Only prime knots in the interval can contribute to the quadratic remainder. -/
theorem margin_affine_lower {n h : ℕ} (hn : 0 < n) (hh : 2*h ≤ n) :
    ∃ s : ℝ, ∀ j ∈ Icc (n-h) (n+h),
      margin n + s*((j:ℝ)-n) - 36*(h:ℝ)^2*Real.log (2*n)/n ≤ margin j := by
  refine ⟨slope n h, fun j hj => ?_⟩
  have b := one_kink_sum (c := 1) hn hh hj (by decide) (by decide)
  simp only [one_mul] at b
  have d := one_kink_sum (c := 4) hn hh hj (by decide) (by decide)
  have eb : (∑ p ∈ primes (n+h), localError n j p) ≤
      2*(∑ p ∈ primes (n+h), coefficient p*remainder n j p) +
        ∑ p ∈ primes (n+h), coefficient p*remainder n j (4*p) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p _
    have coeff : 0 ≤ coefficient p := div_nonneg (Real.log_natCast_nonneg _) (by positivity)
    unfold localError
    nlinarith [mul_nonneg coeff (remainder_nonneg n j (2*p))]
  have hh2 : (h:ℝ) ≤ (h:ℝ)^2 := by
    rcases Nat.eq_zero_or_pos h with rfl | hp
    · norm_num
    · have a : (1:ℝ) ≤ h := by exact_mod_cast hp
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) h) (sub_nonneg.mpr a)]
  have logpos : 0 ≤ Real.log (2*n) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*n by omega))
  have scale := mul_le_mul_of_nonneg_right hh2 (div_nonneg logpos (Nat.cast_nonneg n))
  rw [expand_margin hj]
  linear_combination eb + 2*b + d + 12*scale

#print axioms margin_affine_lower

/-- The margin is discretely concave at every positive integer other than a doubled prime. -/
theorem margin_concave_at_non_double {n : ℕ} (hn : 0 < n)
    (clear : ∀ p : ℕ, p.Prime → n ≠ 2*p) :
    margin (n-1 : ℕ) + margin (n+1 : ℕ) ≤ 2*margin n := by
  have below (j : ℕ) (hj : j ∈ Icc (n-1) (n+1)) :
      margin j ≤ margin n + slope n 1*((j:ℝ)-n) := by
    rw [expand_margin (h := 1) hj]
    apply sub_le_self
    apply Finset.sum_nonneg
    intro p hp
    have ne := clear p (Nat.mem_primesLE.mp hp).2
    obtain ⟨lo,hi⟩ := mem_Icc.mp hj
    have zero : remainder n j (2*p) = 0 := by
      by_cases k : 2*p ≤ n
      · have h : (↑(2*p:ℕ):ℝ) ≤ j := by exact_mod_cast (show 2*p ≤ j by omega)
        simp only [remainder, if_pos k, max_eq_right (sub_nonpos.mpr h)]
      · have h : (j:ℝ) ≤ ↑(2*p:ℕ) := by exact_mod_cast (show j ≤ 2*p by omega)
        simp only [remainder, if_neg k, kink, max_eq_right (sub_nonpos.mpr h)]
    unfold localError
    rw [zero, mul_zero, sub_zero]
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) (by positivity))
      (add_nonneg (mul_nonneg (by norm_num) (remainder_nonneg ..)) (remainder_nonneg ..))
  have left := below (n-1) (mem_Icc.mpr ⟨le_rfl,by omega⟩)
  have right := below (n+1) (mem_Icc.mpr ⟨by omega,le_rfl⟩)
  have cancel : slope n 1*((↑(n-1:ℕ):ℝ)-n) + slope n 1*((↑(n+1:ℕ):ℝ)-n) = 0 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega)]
    push_cast
    ring
  linarith

end RiemannReduction.PrimeGrid
