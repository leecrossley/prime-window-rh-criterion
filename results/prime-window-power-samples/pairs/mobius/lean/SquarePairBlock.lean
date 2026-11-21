import SquarePairDiagonal

/-! An arbitrary fixed saving in the mean square of the unpaired terms gives
the published sign test on the same integer bases. -/

open Finset
namespace RiemannReduction.DivisorBand
noncomputable section

/-- Integer samples on the short block in the published unequal-pair criterion. -/
def squarePairBlock (K : ℕ) : Finset ℕ :=
  Icc K ⌊4*(K : ℝ)*Real.sqrt (Real.log K)⌋₊

def cofinalRemainderBudget (η : ℝ) : Prop :=
  ∀ u : ℕ, ∃ K ≥ u,
    ∑ k ∈ squarePairBlock K, (unpairedTail k (k*k.sqrt)/k)^2 ≤
      η * ∑ k ∈ squarePairBlock K, centeredTentDiagonal ((k : ℝ)^2)/(k : ℝ)^2

def cofinalSquarePairSign : Prop :=
  ∀ u : ℕ, ∃ K ≥ u, ∑ k ∈ squarePairBlock K,
    ((centeredTentSum ((k : ℝ)^2))^2-centeredTentDiagonal ((k : ℝ)^2))/(k : ℝ)^2 ≤ 0

theorem late_pair_sign_of_fractional_budget {η : ℝ} (h1 : η < 1) :
    ∃ u : ℕ, ∀ I : Finset ℕ, (∀ k ∈ I, u ≤ k) →
      ∑ k ∈ I, (unpairedTail k (k*k.sqrt)/k)^2 ≤ η *
        ∑ k ∈ I, centeredTentDiagonal ((k : ℝ)^2)/(k : ℝ)^2 →
      ∑ k ∈ I, ((centeredTentSum ((k : ℝ)^2))^2-centeredTentDiagonal ((k : ℝ)^2))/(k : ℝ)^2 ≤ 0 := by
  let a := (1-η)/2
  let g := 1-(1+a)*η
  let b := (1+1/a)*118^2
  have pa : 0 < a := by dsimp [a]; linarith
  have pg : 0 < g := by
    have cap := mul_le_mul_of_nonneg_left h1.le pa.le
    dsimp [g,a] at *
    nlinarith only [h1, cap]
  obtain ⟨v, hv⟩ := square_diagonal_diverges (b/g)
  refine ⟨max (108^2) v, ?_⟩
  intro I hi hR
  let diag := ∑ k ∈ I, centeredTentDiagonal ((k : ℝ)^2)/(k : ℝ)^2
  have margin : (I.card : ℝ)*b ≤ g*diag := by
    dsimp [diag]
    rw [mul_sum, ← nsmul_eq_mul]
    simpa only [sum_const, nsmul_eq_mul, mul_comm] using
      (sum_le_sum (s := I) (f := fun _ => b) (fun k hk =>
        (div_le_iff₀ pg).mp (hv k (max_le_iff.mp (hi k hk)).2)))
  have energy := centered_square_budget I (fun k hk => (max_le_iff.mp (hi k hk)).1) pa
  have bound := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 1+a)
  have total : (1+a)*(η*diag) = diag-g*diag := by dsimp [g]; ring
  change _ ≤ (1+a)*_+(I.card : ℝ)*(1+1/a)*118^2 at energy
  change _ ≤ (1+a)*(η*diag) at bound
  rw [total] at bound
  change _ ≤ (1-(1+a)*η)*diag at margin
  rw [show (I.card : ℝ)*(1+1/a)*118^2 = (I.card : ℝ)*b by dsimp [b]; ring] at energy
  simp_rw [sub_div, ← div_pow, Finset.sum_sub_distrib]
  change _-diag ≤ 0
  linarith only [energy, bound, margin]

theorem cofinal_pair_sign_of_remainder_budget {η : ℝ} (h1 : η < 1)
    (budget : cofinalRemainderBudget η) : cofinalSquarePairSign := by
  obtain ⟨u, sign⟩ := late_pair_sign_of_fractional_budget h1
  intro v
  obtain ⟨K, late, bound⟩ := budget (max u v)
  exact ⟨K, (le_max_right _ _).trans late, sign _ (fun k hk =>
    ((le_max_left _ _).trans late).trans (mem_Icc.mp hk).1) bound⟩

#print axioms late_pair_sign_of_fractional_budget
#print axioms cofinal_pair_sign_of_remainder_budget

end
end RiemannReduction.DivisorBand
