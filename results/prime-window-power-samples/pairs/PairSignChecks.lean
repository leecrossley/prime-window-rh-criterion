import Mathlib

/-! Finite identities for the dyadic pair statistic and the theta comparison. -/

namespace PrimePairSign

theorem unequal_pairs {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s.erase i, v i * v j) =
      (∑ i ∈ s, v i)^2 - (∑ i ∈ s, (v i)^2) := by
  apply eq_sub_iff_add_eq.mpr
  rw [← Finset.sum_add_distrib, pow_two, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum, pow_two]
  exact Finset.sum_erase_add s (fun j => v i * v j) hi

theorem centered_divisors (n : ℕ) :
    (∑ m ∈ n.divisors, (ArithmeticFunction.vonMangoldt m - 1)) =
      Real.log n - (n.divisors.card : ℝ) := by
  simp [Finset.sum_sub_distrib, ArithmeticFunction.vonMangoldt_sum]

theorem weighted_divisors (s : Finset ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ s, ∑ m ∈ n.divisors, (ArithmeticFunction.vonMangoldt m - 1) * g n) =
      ∑ n ∈ s, (Real.log n - (n.divisors.card : ℝ)) * g n := by
  simp_rw [← Finset.sum_mul, centered_divisors]

theorem two_sided_corners {p m r B : ℝ}
    (hp : 0 ≤ p) (hm : 0 ≤ m) (hr : 0 ≤ r)
    (outer : p + r/2 ≤ B) (middle : 3*m/2 ≤ B) :
    |p - 3*m/2 + r/2| ≤ B := by
  rw [abs_le]
  constructor <;> linarith

theorem corner_moments :
    (1 + (1/2 : ℝ) = 3/2) ∧ (1 + 4*(1/2 : ℝ) = 2*(3/2)) := by norm_num

theorem finite_sign {a d : ℝ} (ha : |a| < 3/10) (hd : 108/1000 < d) :
    a^2 - d < 0 := by
  have h : |a|^2 < (3/10 : ℝ)^2 := by
    nlinarith [abs_nonneg a, mul_pos (sub_pos.mpr ha) (show 0 < 3/10 + |a| by positivity)]
  rw [sq_abs] at h
  linarith

theorem logarithmic_sign {a d : ℝ} (ha : |a| < 45/100) (hd : 21/100 < d) :
    a^2 - d < -(3/400) := by
  have h : |a|^2 < (45/100 : ℝ)^2 := by
    nlinarith [abs_nonneg a, mul_pos (sub_pos.mpr ha) (show 0 < 45/100 + |a| by positivity)]
  rw [sq_abs] at h
  linarith

theorem residual_energy (s v : ℝ) : s^2 - (s-v)^2 = 2*s*v-v^2 := by ring

/-- The step which moves a real-scale detector to the unweighted sum of squares.
    Each square cell has weight at most b, and the total mass is at most one. -/
theorem cell_energy {ι : Type*} (s : Finset ι) (w v : ι → ℝ) (b : ℝ)
    (nonneg : ∀ i ∈ s, 0 ≤ w i) (cell : ∀ i ∈ s, w i ≤ b)
    (mass : ∑ i ∈ s, w i ≤ 1) :
    (∑ i ∈ s, w i * v i)^2 ≤ b * ∑ i ∈ s, (v i)^2 := by
  let m := ∑ i ∈ s, w i * v i
  have pos : 0 ≤ ∑ i ∈ s, w i * (v i - m)^2 := by
    exact Finset.sum_nonneg fun i hi => mul_nonneg (nonneg i hi) (sq_nonneg _)
  have expand : ∀ i, w i * (v i - m)^2 =
      w i * (v i)^2 - 2*m*(w i * v i) + m^2 * w i := by intro i; ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at pos
  change 0 ≤ (∑ i ∈ s, w i * (v i)^2) - 2*m*m + m^2 * (∑ i ∈ s, w i) at pos
  have h := mul_le_mul_of_nonneg_left mass (sq_nonneg m)
  calc
    _ = m^2 := rfl
    _ ≤ ∑ i ∈ s, w i * (v i)^2 := by nlinarith
    _ ≤ ∑ i ∈ s, b * (v i)^2 :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (cell i hi) (sq_nonneg _)
    _ = _ := (Finset.mul_sum ..).symm

#print axioms unequal_pairs
#print axioms centered_divisors
#print axioms weighted_divisors
#print axioms two_sided_corners
#print axioms corner_moments
#print axioms finite_sign
#print axioms logarithmic_sign
#print axioms residual_energy
#print axioms cell_energy

end PrimePairSign
