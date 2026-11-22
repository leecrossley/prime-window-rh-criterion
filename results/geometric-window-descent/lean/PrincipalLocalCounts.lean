import AtCharacter
import PrincipalCountWindow
import PrincipalHostCharacters

/-! The outside-prime estimate and the joint cohomological window are pointwise
in the chosen Dirichlet character. At conductor one every odd-order character
of a host is trivial. This removes the third symplectic count from the window. -/

open Lean Elab Command in
run_cmd liftTermElabM do
  let specialize := RiemannReduction.CharacterRestriction.restrictProof
  specialize `UpperTheory.V.HV.sumIn `RiemannReduction.LocalCases.sumInside 5 4 #[0]
  specialize `UpperTheory.V.HV.sumOut `RiemannReduction.LocalCases.sumOutside 5 4 #[0,1,2,3]
  specialize `UpperTheory.V.HV.point `RiemannReduction.LocalCases.pointBound 3 2 #[0,1]
  specialize `UpperTheory.V.HV.thmHV `RiemannReduction.LocalCases.heightBound 5 4 #[0]
  specialize `UpperTheory.V.jointWin_of `RiemannReduction.LocalCases.jointWindow 6 5 #[4]

noncomputable section
open Formalism.HC Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.HV
open RiemannReduction.LocalCases
namespace RiemannReduction.ConductorOne

def SecondCaseAt (χ : PChar) : Prop :=
  ∃ C : ℕ, ∀ h : UpperTheory.V.HV.Host, h.chi = χ → ∀ t : ℕ, h.Big t →
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
      [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t →
      ∀ ψ ∈ h.X c e, h.CaseII l e ψ → VLe Ω c e ψ (((l : ℝ) * h.N * e) ^ C)

theorem window_without_third_count (duality : GlobalTheory.Published.PoitouTateDuality)
    (finitePlaces : LocalFinitenessK) (localDuality : LocalTateDualityK)
    {c : ℝ} (generators : LemmaK c) {B : BConst} (twoAndLayers : ThmBab B 401)
    (caseI : CountI) (caseII : SecondCaseAt PChar.one) (caseV : CountV) (trivial : CountZ) :
    VWinAt PChar.one 401 := by
  have outside := sumOutside PChar.one (caseI _) (trivial _) caseII (by
    refine ⟨0, ?_⟩
    intro h one t _ Ω _ _ _ l _ co e _ _ _ ψ hψ impossible
    exact (case_three_empty one (h.mem_X.1 hψ).1 l e impossible).elim)
  have inside := sumInside caseV (countVs duality finitePlaces localDuality _ generators) countIV PChar.one caseII
  have height := heightBound B 401 (by norm_num) PChar.one (pointBound PChar.one inside outside)
  have both := jointWindow (by norm_num : (0:ℝ) < 401) twoAndLayers PChar.one height
  apply principal_window_of_joint_pages (by norm_num)
  intro eps hp hlt e he
  exact both eps 4 hp hlt e _ (admissible_of_pageN hp hlt (by norm_num) he)

end RiemannReduction.ConductorOne
