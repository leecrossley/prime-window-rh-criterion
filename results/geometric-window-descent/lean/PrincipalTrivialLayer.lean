import PrincipalHostCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.TorsClass

/-! At conductor one the fourth case is the trivial character. Its contribution
at 3 vanishes in every allowable twist, and at 7 it vanishes in twists divisible by six. -/
noncomputable section
open Formalism.HC Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.HV
namespace RiemannReduction.ConductorOne

private theorem trivial_four {h : UpperTheory.V.HV.Host} (one : h.chi = PChar.one)
    {t : ℕ} (big : h.Big t) {l : ℕ} [prime : Fact l.Prime] (odd : l ≠ 2) (c : Coef l)
    {e : ℕ} {ψ : DirichletCharacter c.O h.N} (member : ψ ∈ h.X c e) (caseIV : h.CaseIV l e ψ) :
    ψ = 1 ∧ Even e := by
  have small := (bchiFacts h t big).1 l caseIV.1
  have trivial := case_four_is_trivial one (h.mem_X.1 member).1 prime.out odd small.1.ne small.2.ne caseIV
  refine ⟨trivial, ?_⟩
  have parity := (h.mem_X.1 member).2
  unfold PsiEven at parity
  rw [trivial, MulChar.one_apply (isUnit_one.neg)] at parity
  by_contra hne
  rw [(Nat.not_even_iff_odd.1 hne).neg_one_pow] at parity
  have h2 : (2 : c.O) = 0 := by linear_combination parity
  exact two_ne_zero h2

theorem trivial_four_length {h : UpperTheory.V.HV.Host} (one : h.chi = PChar.one)
    {t : ℕ} (big : h.Big t) (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] (odd : l ≠ 2) (c : Coef l) {e : ℕ} {ψ : DirichletCharacter c.O h.N}
    (member : ψ ∈ h.X c e) (caseIV : h.CaseIV l e ψ) (twist : l - 1 ∣ e) : Vlen Ω c e ψ = 0 := by
  have := c.dvr
  have := c.fin
  obtain ⟨rfl, _⟩ := trivial_four one big odd c member caseIV
  have ht : Chr.dirG ℚ Ω (1 : DirichletCharacter c.O h.N) = 1 := by
    ext g
    simp [Chr.dirG]
  unfold Vlen
  rw [ht]
  exact le_antisymm ((Chr.V'_le_V l h.N e 1).trans
    (UpperTheory.V.X.zOne Ω l c.O odd e (by have := caseIV.2.1; omega) twist).le) bot_le

theorem case_four_at_three {h : UpperTheory.V.HV.Host} (one : h.chi = PChar.one)
    {t : ℕ} (big : h.Big t) (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (c : Coef 3) {e : ℕ} {ψ : DirichletCharacter c.O h.N} (member : ψ ∈ h.X c e)
    (caseIV : h.CaseIV 3 e ψ) : Vlen Ω c e ψ = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hev := (trivial_four one big (by decide : 3 ≠ 2) c member caseIV).2
  exact trivial_four_length one big Ω (by decide) c member caseIV (even_iff_two_dvd.mp hev)

theorem case_four_at_seven {h : UpperTheory.V.HV.Host} (one : h.chi = PChar.one)
    {t : ℕ} (big : h.Big t) (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (c : Coef 7) {e : ℕ} {ψ : DirichletCharacter c.O h.N} (member : ψ ∈ h.X c e)
    (caseIV : h.CaseIV 7 e ψ) (twist : 6 ∣ e) : Vlen Ω c e ψ = 0 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact trivial_four_length one big Ω (by decide) c member caseIV twist

#print axioms case_four_at_three
#print axioms case_four_at_seven
end RiemannReduction.ConductorOne
