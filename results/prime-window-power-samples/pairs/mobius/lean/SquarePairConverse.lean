import SquarePairBlock
import SquareSignedConverse

/-! Under RH the unpaired square energy is eventually smaller than every
fixed positive fraction of its diagonal, including on the actual short blocks. -/

open Finset
namespace RiemannReduction.DivisorBand

noncomputable section

theorem remainder_energy_of_rh (rh : RiemannHypothesis) {η : ℝ} (hη : 0 < η) :
    ∃ u : ℕ, ∀ k ≥ u, (unpairedTail k (k*k.sqrt)/k)^2 ≤
      η * (centeredTentDiagonal ((k : ℝ)^2)/(k : ℝ)^2) := by
  obtain ⟨C, hC, bound⟩ := square_root_bound_of_rh rh
  obtain ⟨v, diag⟩ := square_diagonal_diverges ((C+117)^2/η)
  refine ⟨max (108^2) v, ?_⟩
  intro k hk
  obtain ⟨hi, hv⟩ := max_le_iff.mp hk
  have k3 : 3 ≤ k := by norm_num at hi; omega
  have kp : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have id := D_nat (k^2)
  rw [Nat.cast_pow] at id
  obtain ⟨lo, up⟩ := remainder_margin_comparison hi
  rw [← id] at lo up
  obtain ⟨dl, du⟩ := abs_le.mp (bound k k3)
  have ab : |unpairedTail k (k*k.sqrt)/k| ≤ C+117 := by
    rw [abs_div, abs_of_pos kp, div_le_iff₀ kp, abs_le]
    constructor <;> linarith
  have sqr := pow_le_pow_left₀ (abs_nonneg _) ab 2
  rw [sq_abs] at sqr
  exact sqr.trans (by simpa only [mul_comm] using (div_le_iff₀ hη).mp (diag k hv))

theorem cofinal_remainder_budget_of_rh (rh : RiemannHypothesis) {η : ℝ} (hη : 0 < η) :
    cofinalRemainderBudget η := by
  obtain ⟨u, bound⟩ := remainder_energy_of_rh rh hη
  intro v
  let K := max u v
  refine ⟨K, le_max_right _ _, ?_⟩
  rw [mul_sum]
  exact sum_le_sum (fun k hk => bound k ((le_max_left u v).trans (mem_Icc.mp hk).1))

/-- The analytic implication from the published short-block theorem is explicit.
    The arithmetic transfer and the reverse implication are proved in this module tree. -/
theorem remainder_budget_iff_rh_of_short_block_theorem
    (shortBlock : cofinalSquarePairSign → RiemannHypothesis) {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    cofinalRemainderBudget η ↔ RiemannHypothesis :=
  ⟨fun budget => shortBlock (cofinal_pair_sign_of_remainder_budget h1 budget),
    fun rh => cofinal_remainder_budget_of_rh rh h0⟩

#print axioms remainder_budget_iff_rh_of_short_block_theorem
#print axioms remainder_energy_of_rh
#print axioms cofinal_remainder_budget_of_rh

end
end RiemannReduction.DivisorBand
