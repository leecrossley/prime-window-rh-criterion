import PrincipalMinusField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Iv
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ThmBcOfPsiBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOrthogonalityHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.PoitouTateNormalisedHolds

/-! Odd-prime estimates for fields of dyadic degree. The residue estimate uses
    the imported Poitou--Tate and reciprocity arguments. No general
    bad-degree Stickelberger estimate enters the proof. -/

noncomputable section
open NumberField Formalism.HC Formalism.GaloisCohomology
open UpperTheory.V UpperTheory.Top

namespace RiemannReduction.ConductorOne

theorem odd_residue_bound : Odd.PrimeBound :=
  Odd.primeBound_of <| ML.iv
    (GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised
      PositivityTheory.Lit1.PTN.poitouTateNormalised_holds)
    GlobalTheory.unramifiedOrthogonality_holds

/-- The estimate for an arbitrary dyadic-degree CM field embedded at level N. -/
theorem dyadic_field_minus_bound {E : Type} [Field E] [NumberField E] [IsCMField E]
    {N t u : ℕ} (hN : 0 < N) (ht : 2 ≤ t) (dyadic : Module.finrank ℚ E ∣ 2^u)
    (emb : Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)) :
    VVminusLe E t (3 * (Module.finrank ℚ E : ℝ) * (t : ℝ)^2 * Real.log ((t : ℝ)*N)) := by
  apply minus_budget_of_twist_bounds hN ht
  intro Ω _ _ _ ld e he
  have h := odd_residue_bound E Ω N hN emb ld e he
  have coprime (p : ℕ) (hpr : p.Prime) (hp : p ≠ 2) : ¬ p ∣ Module.finrank ℚ E := by
    intro hd
    exact hp ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp
      (hpr.dvd_of_dvd_pow (hd.trans dyadic)))
  refine ⟨fun p pr hp => h.1 p hp (coprime p pr.out hp), ?_⟩
  intro S hS
  exact h.2 S (fun p hmem => ⟨hS p hmem, coprime p p.2 (hS p hmem)⟩)

theorem principal_field_minus_bound {E : Type} [Field E] [NumberField E] [IsCMField E]
    {j q d t : ℕ} (hj : 2 ≤ j) (hp : PrimePair 1 q d)
    (field : IsChiField PChar.one j q d E) (ht : 2 ≤ t) :
    let n : ℕ := 2^(j+2)
    VVminusLe E t (3 * (n : ℝ) * (t : ℝ)^2 * Real.log ((t : ℝ)*(n*(q*d) : ℕ))) := by
  let n : ℕ := 2^(j+2)
  have hn : 0 < n := pow_pos (by decide) _
  have hN : 0 < n*(q*d) := Nat.mul_pos hn (Nat.mul_pos hp.1.pos hp.2.2.1.pos)
  obtain ⟨divides, emb⟩ := principal_cyclotomic_data hj hp E field
  have res := dyadic_field_minus_bound hN ht divides emb
  have hd : (Module.finrank ℚ E : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn divides
  have hm : 0 ≤ Real.log ((t : ℝ) * (n * (q*d) : ℕ)) := Real.log_nonneg (by
    exact_mod_cast Nat.mul_pos (by omega : 0 < t) hN)
  change VVminusLe E t (3 * (n : ℝ) * (t : ℝ)^2 * Real.log ((t : ℝ)*(n*(q*d) : ℕ)))
  intro Ω _ _ _ ld
  obtain ⟨fin, bd⟩ := res Ω ld
  refine ⟨fin, fun S hS => (bd S hS).trans ?_⟩
  gcongr

end RiemannReduction.ConductorOne
