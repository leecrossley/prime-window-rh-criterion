import PrincipalMinusResidues

/-! The odd-minus allowance at the least cyclotomic conductor of a principal
    host field. The dyadic degree removes every bad odd prime. -/

noncomputable section
open NumberField Formalism.HC UpperTheory.V UpperTheory.Top
namespace RiemannReduction.ConductorOne

theorem principal_minus_at_conductor {E : Type} [Field E] [NumberField E] [IsCMField E]
    {j q d t : ℕ} (hj : 2 ≤ j) (hp : PrimePair 1 q d)
    (field : IsChiField PChar.one j q d E) (ht : 2 ≤ t) :
    VVminusLe E t (minusBound 0 (AbF.ofChar PChar.one).deg
      (Module.finrank ℚ E) (condF E) t) := by
  obtain ⟨divides, emb⟩ := principal_cyclotomic_data hj hp E field
  have hN : 0 < 2^(j+2) * (q*d) := Nat.mul_pos (pow_pos (by decide) _)
    (Nat.mul_pos hp.1.pos hp.2.2.1.pos)
  have least : 0 < condF E ∧ Nonempty (E →ₐ[ℚ] CyclotomicField (condF E) ℚ) := by
    unfold condF
    exact Nat.sInf_mem (s := {n : ℕ | 0 < n ∧ Nonempty (E →ₐ[ℚ] CyclotomicField n ℚ)})
      ⟨_, hN, emb⟩
  simpa only [minusBound, zero_mul, add_zero] using
    dyadic_field_minus_bound least.1 ht divides least.2

end RiemannReduction.ConductorOne
