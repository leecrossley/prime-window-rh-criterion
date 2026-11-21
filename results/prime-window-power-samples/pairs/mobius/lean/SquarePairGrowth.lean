import SquarePairConverse

/-! Transfer the growth alternative in the published short-block argument.
    A bounded residual-to-diagonal ratio, with any fixed allowance, suffices
    once the published off-line growth theorem for the centered energy is supplied. -/

open Finset
namespace RiemannReduction.DivisorBand
noncomputable section

def shortCenteredEnergy (K : ℕ) : ℝ :=
  ∑ k ∈ squarePairBlock K, (centeredTentSum ((k : ℝ)^2)/k)^2

def shortRemainderEnergy (K : ℕ) : ℝ :=
  ∑ k ∈ squarePairBlock K, (unpairedTail k (k*k.sqrt)/k)^2

def shortDiagonal (K : ℕ) : ℝ :=
  ∑ k ∈ squarePairBlock K, centeredTentDiagonal ((k : ℝ)^2)/(k : ℝ)^2

/-- Exceed every fixed multiple of the same diagonal on every sufficiently late block. -/
def exceedsDiagonal (energy : ℕ → ℝ) : Prop :=
  ∀ B : ℝ, ∃ u : ℕ, ∀ K ≥ u, B*shortDiagonal K < energy K

theorem late_centered_energy_le_two_remainders :
    ∃ u : ℕ, ∀ K ≥ u, shortCenteredEnergy K ≤ 2*shortRemainderEnergy K+shortDiagonal K := by
  obtain ⟨v, big⟩ := square_diagonal_diverges (2*118^2)
  refine ⟨max v (108^2), ?_⟩
  intro K hk
  let I := squarePairBlock K
  have inside (k : ℕ) (h : k ∈ I) : max v (108^2) ≤ k :=
    hk.trans (mem_Icc.mp h).1
  have compare := centered_square_budget I (fun k h => (le_max_right _ _).trans (inside k h))
    (a := 1) (by norm_num)
  have diag := sum_le_sum (s := I) (f := fun _ => (2*118^2 : ℝ))
    (fun k h => big k ((le_max_left _ _).trans (inside k h)))
  simp only [sum_const, nsmul_eq_mul] at diag
  change _ ≤ 2 * _ + _
  dsimp only [shortCenteredEnergy, shortRemainderEnergy, shortDiagonal]
  dsimp only [I] at compare diag
  norm_num at compare
  linarith only [diag, compare]

/-- The full off-line growth of the published centered energy forces growth
    of the actual complementary Möbius energy relative to its diagonal. -/
theorem remainder_growth_of_centered_growth (growth : exceedsDiagonal shortCenteredEnergy) :
    exceedsDiagonal shortRemainderEnergy := by
  obtain ⟨u, compare⟩ := late_centered_energy_le_two_remainders
  intro B
  obtain ⟨v, above⟩ := growth (2*B+1)
  refine ⟨max u v, ?_⟩
  intro K hk
  obtain ⟨hu, hv⟩ := max_le_iff.mp hk
  nlinarith only [compare K hu, above K hv]

/-- The named analytic premise follows from the off-line growth and diagonal
    asymptotic in SHORT-BLOCKS.md. No particular numerical saving is required. -/
theorem bounded_short_remainder_ratio_iff_rh
    (offLine : ¬RiemannHypothesis → exceedsDiagonal shortCenteredEnergy) :
    (∃ B : ℝ, cofinalRemainderBudget B) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨B, budget⟩
    by_contra failure
    obtain ⟨u, bad⟩ := remainder_growth_of_centered_growth (offLine failure) B
    obtain ⟨K, hk, good⟩ := budget u
    exact (not_lt_of_ge good) (bad K hk)
  · intro rh
    exact ⟨1, cofinal_remainder_budget_of_rh rh (by norm_num)⟩

#print axioms late_centered_energy_le_two_remainders
#print axioms remainder_growth_of_centered_growth
#print axioms bounded_short_remainder_ratio_iff_rh

end
end RiemannReduction.DivisorBand
