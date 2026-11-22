import MizusawaTower
import SecondSeedWindow
import FiniteFrameRH

/-! The geometric proof with the rank-three ordinary Iwasawa module as its
explicit literature input. -/

noncomputable section

open Formalism.HC UpperTheory.Top RiemannGaussian.AlpogeWindow

namespace RiemannReduction.ConductorOne

theorem rh_of_mizusawa_rank_three (rank : RiemannReduction.Mizusawa.RankThree) :
    RiemannHypothesis := by
  let galois := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let localParameters := UpperTheory.Zero.LLC.recTExists
  let literature : ArchivedInputs.OpenLiteratureStatements := ⟨galois, localParameters, galois⟩
  exact RiemannReduction.WithFrame.RiemannGaussian.AlpogeWindow.rh_of_principal_archived_grid
    Formalism.HN.finite_frame_compat_of (ArchivedInputs.published_results_eigen literature)
    (ArchivedInputs.principal_archived_covolume literature) localParameters
    (supplyChi PChar.one (RiemannReduction.PrincipalLayer.window_from_second_seed
      (RiemannReduction.Mizusawa.ordinary_three_input rank)
      (principal_rankN_inputs literature galois)))

#print axioms rh_of_mizusawa_rank_three

end RiemannReduction.ConductorOne
