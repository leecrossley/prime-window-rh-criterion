import PrincipalJointWindow
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.JointWinOfCounts

/-! Specializing the archive's simultaneous prime-two and odd-plus counts
    now suffices for the principal height-401 window. -/

noncomputable section
open Formalism.HC Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.HV
namespace RiemannReduction.ConductorOne

theorem principal_window_from_counts (duality : GlobalTheory.Published.PoitouTateDuality)
    (finitePlaces : LocalFinitenessK) (localDuality : LocalTateDualityK)
    {c : ℝ} (generators : LemmaK c) {B : BConst} (twoAndLayers : ThmBab B 401)
    (caseI : CountI) (caseII : CountII) (caseIII : CountIII) (caseV : CountV) (trivial : CountZ) :
    VWinAt PChar.one 401 :=
  principal_window_of_joint (by norm_num)
    (jointWin_of_counts duality finitePlaces localDuality generators twoAndLayers
      caseI caseII caseIII caseV trivial)

#print axioms principal_window_from_counts

end RiemannReduction.ConductorOne
