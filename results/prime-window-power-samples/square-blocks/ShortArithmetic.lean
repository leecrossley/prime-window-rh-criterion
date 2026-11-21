import Mathlib

namespace ShortArithmetic

/-- The chord of a single ramp, less its value at the sample. -/
theorem ramp_chord (a b x t : ℝ) (hab : a < b) (hat : a ≤ t) (htb : t ≤ b) :
    ((b - x) * max (a - t) 0 + (x - a) * max (b - t) 0) / (b - a) -
        max (x - t) 0 =
      (min x t - a) * (b - max x t) / (b - a) := by
  rw [max_eq_right (sub_nonpos.mpr hat), max_eq_left (sub_nonneg.mpr htb)]
  have hd : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  rcases le_total x t with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h, max_eq_right h]
    ring
  · rw [max_eq_left (sub_nonneg.mpr h), min_eq_right h, max_eq_left h]
    field_simp
    ring

/-- Centre the prime sum by the chord of the quadratic main term. -/
theorem quadratic_chord (a b x : ℝ) (hab : a < b) :
    ((b - x) * (a ^ 2 / 2) + (x - a) * (b ^ 2 / 2)) / (b - a) -
        x ^ 2 / 2 = (x - a) * (b - x) / 2 := by
  have hd : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  field_simp
  ring

/-- Integrating the two pieces of the squared, unit-interval kernel. -/
theorem kernel_square_pieces (y : ℝ) :
    (1-y)^2 * (y^3 / 3) + y^2 * ((1-y)^3 / 3) = y^2 * (1-y)^2 / 3 := by
  ring

theorem diagonal_constant : (2 : ℚ)^3 * 2 * ((1/3 - 1/2 + 1/5) / 3) = 8/45 := by
  norm_num

/-- The signed mean removes exactly one component of a finite second moment. -/
theorem sum_variance {ι : Type*} (s : Finset ι) (f : ι → ℝ) (m : ℝ)
    (hm : ∑ i ∈ s, f i = (s.card : ℝ) * m) :
    ∑ i ∈ s, (f i)^2 = ∑ i ∈ s, (f i - m)^2 + (s.card : ℝ) * m^2 := by
  have hs : ∀ i ∈ s, (f i - m)^2 = (f i)^2 - f i * (2*m) + m^2 := by
    intro i hi
    ring
  rw [Finset.sum_congr rfl hs, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hm]
  simp
  ring

/-- When passing between neighbouring blocks, the right endpoints skip at most one integer. -/
theorem uncovered_endpoint (k m : ℕ) (e : ℕ → ℕ)
    (hle : e k ≤ m) (hgt : m < e (k+1)) (hstep : e (k+1) ≤ e k + 2) :
    m = e k ∨ m = e k + 1 := by omega

/-- One-sided control of the centred off-diagonal sum is sufficient. -/
theorem residual_bound (energy diagonal error : ℝ)
    (bound : energy - diagonal ≤ error) : energy ≤ diagonal + error := by linarith

/-- Split a sum into values below a threshold and a bounded exceptional set. -/
theorem sum_le_threshold_add_tail {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (threshold bound : ℝ) (ht : 0 ≤ threshold) (hb : ∀ i ∈ s, f i ≤ bound) :
    ∑ i ∈ s, f i ≤ (s.card : ℝ) * threshold +
      ((s.filter fun i => threshold < f i).card : ℝ) * bound := by
  classical
  calc
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, (threshold + if threshold < f i then bound else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with h
      · linarith [hb i hi]
      · simpa using le_of_not_gt h
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp

theorem density_margin : 3 * (1 - (87:ℚ)/100) / (3 * ((87:ℚ)/100) - 1) < 1/4 := by
  norm_num

#print axioms ramp_chord
#print axioms quadratic_chord
#print axioms kernel_square_pieces
#print axioms diagonal_constant
#print axioms sum_variance
#print axioms uncovered_endpoint
#print axioms residual_bound
#print axioms sum_le_threshold_add_tail
#print axioms density_margin

end ShortArithmetic
