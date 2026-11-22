import CyclotomicEight
import SecondSeedWindow
import FiniteFrameRH

/-! The existing geometric endpoint with its three-generator input proved from units. -/

noncomputable section

open Formalism.HC UpperTheory.Top RiemannGaussian.AlpogeWindow

namespace RiemannReduction.ConductorOne

theorem rh_from_tame_units :
    RiemannHypothesis := by
  let galois := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let localParameters := UpperTheory.Zero.LLC.recTExists
  let literature : ArchivedInputs.OpenLiteratureStatements := ⟨galois, localParameters, galois⟩
  exact RiemannReduction.WithFrame.RiemannGaussian.AlpogeWindow.rh_of_principal_archived_grid
    Formalism.HN.finite_frame_compat_of (ArchivedInputs.published_results_eigen literature)
    (ArchivedInputs.principal_archived_covolume literature) localParameters
    (supplyChi PChar.one (RiemannReduction.PrincipalLayer.window_from_second_seed
      RiemannReduction.TameSigns.ordinary_three_input
      (principal_rankN_inputs literature galois)))

#print axioms rh_from_tame_units

end RiemannReduction.ConductorOne
