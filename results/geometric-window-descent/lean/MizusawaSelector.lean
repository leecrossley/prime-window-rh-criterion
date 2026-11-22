import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Window

/-! Dependence of the dyadic selector on its generator bound.
Here B represents 2 C_K C_t / ε in the existing selector. -/

namespace RiemannReduction.Mizusawa

open UpperTheory.Top UpperTheory.V UpperTheory.V.Win

theorem reference_levels : jZero 2 9 = 6 ∧ jZero 2 3 = 4 := by decide

theorem window_with_three (η C X : ℝ) (exc : Finset ℕ) (hη : 0 < η)
    (hC : η ≤ C) (hX : 1 < X) (hcard : exc.card ≤ 3) :
    ∃ Y : ℝ, InRange (32 * (C / η) ^ 3) X Y ∧
      ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → Good η C exc x := by
  simpa only [show (2 : ℝ) ^ (3+2) = 32 by norm_num] using window 3 η C X exc hη hC hX hcard

theorem selector_three_vs_nine (B : ℝ) :
    (2 : ℝ) ^ (9+2) * B ^ 9 =
      (64 * B ^ 6) * ((2 : ℝ) ^ (3+2) * B ^ 3) := by ring

end RiemannReduction.Mizusawa
