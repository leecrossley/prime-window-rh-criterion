import Mathlib

namespace ShortBlock.SurvivingZeros

/-- The transform of a normalized two-point signed filter.  Its second
    argument is the exponential at the second point of its support. -/
noncomputable def atom (r z : ℂ) : ℂ := r / (r - 1) - z / (r - 1)

theorem atom_mass (r : ℂ) (hr : r ≠ 1) : atom r 1 = 1 := by
  unfold atom
  rw [← sub_div, div_self (sub_ne_zero.mpr hr)]

theorem atom_zero (r : ℂ) : atom r r = 0 := sub_self _

/-- The finite product preserves the chosen mode and kills each competing
    mode, including competitors with the same ordinate and another real part. -/
theorem finite_projection {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (target : ι) (coeff ratio : ι → ℂ) (twist : ι → ι → ℂ)
    (ht : target ∈ s)
    (hmass : ∀ j ∈ s.erase target, ratio j ≠ 1 ∧ twist j target = 1)
    (hdiag : ∀ j ∈ s.erase target, twist j j = ratio j) :
    ∑ i ∈ s, coeff i * ∏ j ∈ s.erase target, atom (ratio j) (twist j i) =
      coeff target := by
  rw [Finset.sum_eq_single target]
  · have hh : ∏ j ∈ s.erase target, atom (ratio j) (twist j target) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      rw [(hmass j hj).2, atom_mass _ (hmass j hj).1]
    rw [hh, mul_one]
  · intro i hi hne
    have he : i ∈ s.erase target := Finset.mem_erase.mpr ⟨hne, hi⟩
    have hz : ∏ j ∈ s.erase target, atom (ratio j) (twist j i) = 0 := by
      apply Finset.prod_eq_zero he
      rw [hdiag i he, atom_zero]
    simp [hz]
  · exact fun h => (h ht).elim

/-- Only samples past the verified height can contribute to the finite
    shell. Bound their squared signed sums after taking account of support. -/
theorem finite_shell_energy {ι : Type*} [DecidableEq ι]
    (block active : Finset ι) (f : ι → ℝ) (u : ℝ) (hsub : active ⊆ block)
    (hoff : ∀ i ∈ block, i ∉ active → f i = 0)
    (hon : ∀ i ∈ active, |f i| ≤ u) :
    ∑ i ∈ block, (f i)^2 ≤ (active.card : ℝ) * u^2 := by
  calc
    ∑ i ∈ block, (f i)^2 = ∑ i ∈ active, (f i)^2 := by
      symm
      apply Finset.sum_subset hsub
      intro i hi ha
      simp [hoff i hi ha]
    _ ≤ ∑ _i ∈ active, u^2 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (f i)^2 = |f i|^2 := (sq_abs _).symm
        _ ≤ u^2 := by
          gcongr
          exact hon i hi
    _ = (active.card : ℝ) * u^2 := by simp

/-- A sign change on integer samples forces a sample no larger in
    absolute value than the largest intervening jump. -/
theorem small_at_crossing (f : ℕ → ℝ) {a b : ℕ} {d : ℝ}
    (hab : a ≤ b) (hd : 0 ≤ d) (ha : f a ≤ 0) (hb : 0 ≤ f b)
    (jump : ∀ n, a ≤ n → n < b → |f (n + 1) - f n| ≤ d) :
    ∃ j, a ≤ j ∧ j ≤ b ∧ |f j| ≤ d := by
  classical
  have hex : ∃ n, a ≤ n ∧ 0 ≤ f n := ⟨b, hab, hb⟩
  let j := Nat.find hex
  have hj : a ≤ j ∧ 0 ≤ f j := Nat.find_spec hex
  have hjb : j ≤ b := Nat.find_min' hex ⟨hab, hb⟩
  refine ⟨j, hj.1, hjb, ?_⟩
  rw [abs_of_nonneg hj.2]
  by_cases heq : a = j
  · simpa [← heq] using ha.trans hd
  · have hpred : a ≤ j - 1 := by omega
    have hlt : j - 1 < j := by omega
    have he : ¬ (a ≤ j - 1 ∧ 0 ≤ f (j - 1)) := Nat.find_min hex hlt
    have hneg : f (j - 1) < 0 := lt_of_not_ge (fun hp => he ⟨hpred, hp⟩)
    have hdiff := (abs_le.mp (jump (j-1) hpred (lt_of_lt_of_le hlt hjb))).2
    have hnext : j - 1 + 1 = j := by omega
    rw [hnext] at hdiff
    linarith

theorem density_width {s a : ℝ} (ha : 0 ≤ a) :
    a * (3 * (1-s)) < 2*s-1 ↔ (1+3*a)/(2+3*a) < s := by
  have hpos : 0 < 2 + 3*a := by linarith
  rw [div_lt_iff₀ hpos]
  constructor <;> intro h <;> nlinarith

theorem jump_exponents :
    2*(7/8:ℝ)-2 = -(1/4) ∧
    2*(7/8:ℝ)-1-2*(397/1000) = -(11/250) ∧
    (397/1000:ℝ)-1+1/4 < 0 := by norm_num

#print axioms finite_projection
#print axioms finite_shell_energy
#print axioms small_at_crossing
#print axioms density_width
#print axioms jump_exponents

end ShortBlock.SurvivingZeros
