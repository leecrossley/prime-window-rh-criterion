import PrincipalTowerFields
import PrincipalMinusSum

noncomputable section
open NumberField Formalism.HC Formalism.GaloisCohomology
open UpperTheory.V UpperTheory.Top

namespace RiemannReduction.ConductorOne

/-- The same cyclotomic realization gives both the ambient conductor and the
    power-of-two degree bound for any representative of the principal host field. -/
theorem principal_cyclotomic_data {j q d : ℕ} (hj : 2 ≤ j) (hp : PrimePair 1 q d)
    (E : Type) [Field E] [NumberField E] (hf : IsChiField PChar.one j q d E) :
    let n : ℕ := 2^(j+2)
    Module.finrank ℚ E ∣ n ∧ Nonempty (E →ₐ[ℚ] CyclotomicField (n*(q*d)) ℚ) := by
  let h : UpperTheory.V.HV.Host := ⟨PChar.one, j, q, d, hj, hp⟩
  have lev := HV.hostLevel h E hf
  have deg := (Chr.levGal E h.N h.H lev).2.1
  have ho : h.o = 1 := orderOf_one
  have hn : h.N = 2^(j+2)*(q*d) := by
    change Nat.lcm (2^(j+2)) 1 * (q*d) = _
    simp
  obtain ⟨emb, _⟩ := lev
  refine ⟨?_, hn ▸ ⟨emb⟩⟩
  rw [deg]
  simpa only [ho, mul_one] using (HV.hostIndex h).1

/-- Sum the prime-by-prime estimates inside a fixed field. -/
theorem minus_budget_of_twist_bounds {E : Type} [Field E] [NumberField E] [IsCMField E]
    {N t : ℕ} (hN : 0 < N) (ht : 2 ≤ t)
    (perTwist : ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
        (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (e : ℕ), 1 ≤ e →
      (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → minusLen (ld p) e ≠ ⊤) ∧
      ∀ S : Finset Nat.Primes, (∀ p ∈ S, (p : ℕ) ≠ 2) →
        ∑ p ∈ S, Real.log (p : ℕ) *
          ((@minusLen E Ω _ _ _ _ _ _ p ⟨p.2⟩ (@ld p ⟨p.2⟩) e).toNat : ℝ) ≤
          Module.finrank ℚ E * Real.log (16 * (N : ℝ)^(e+1+1) * ((e+1).factorial : ℝ))) :
    VVminusLe E t (3 * (Module.finrank ℚ E : ℝ) * (t : ℝ)^2 * Real.log ((t : ℝ)*N)) := by
  intro Ω _ _ _ ld
  refine ⟨fun p _ e hp he _ => (perTwist Ω ld e he).1 p hp, ?_⟩
  intro S hS
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_bernoulli_budgets hN ht (Nat.cast_nonneg _)
  intro e he
  exact (perTwist Ω ld e (Finset.mem_Ico.mp he).1).2 S hS

end RiemannReduction.ConductorOne
