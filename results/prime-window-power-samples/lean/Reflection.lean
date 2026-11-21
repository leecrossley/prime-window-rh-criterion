import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

namespace RiemannReduction
open Complex

/-- A zero outside the trivial list is also a zero of the completed zeta function. -/
private theorem completed_zero {s : ℂ} (hz : riemannZeta s = 0)
    (ht : ¬ ∃ n : ℕ, s = -2 * (n+1)) : completedRiemannZeta s = 0 := by
  have hs : s ≠ 0 := by rintro rfl; norm_num [riemannZeta_zero] at hz
  have hg : Gammaℝ s ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h
    cases n with
    | zero => exact hs (by simpa using hn)
    | succ k => exact ht ⟨k, by simpa [Nat.cast_succ, neg_mul] using hn⟩
  exact (div_eq_zero_iff.mp ((riemannZeta_def_of_ne_zero hs).symm.trans hz)).resolve_right hg

/-- The same right-half-plane hypothesis as Alpöge's final symmetry reduction. -/
theorem rh_of_right (right : ∀ s : ℂ, 1/2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hz ht h1
  refine le_antisymm (not_lt.mp fun h => right s h h1 hz) ?_
  by_contra! h
  have h0 : s ≠ 0 := by rintro rfl; norm_num [riemannZeta_zero] at hz
  apply right (1-s) (by simp [Complex.sub_re]; linarith) (by intro e; apply h0; linear_combination -e)
  rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr h1.symm), completedRiemannZeta_one_sub,
    completed_zero hz ht, zero_div]

#print axioms rh_of_right
end RiemannReduction
