import MizusawaTower
import SecondSeedWindow
import FiniteFrameRH

/-! The same literature input and window assembly with the bound weakened
from three to nine. This controls for the change of arithmetic proof. -/

noncomputable section

open NumberField Formalism.HC Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.Base
  UpperTheory.V.Kum UpperTheory.V.Two UpperTheory.V.Win RiemannGaussian.AlpogeWindow

namespace RiemannReduction.Mizusawa

theorem nine_input_from_three (rank : RankThree) (bounds : TowerBound) :
    RiemannReduction.GaussianTower.TwoInputAt (AbF.ofChar PChar.one) := by
  refine ⟨9, fun q d pair => ?_⟩
  obtain ⟨L, _, _, field⟩ := abExists (base2 (AbF.ofChar PChar.one) q d)
  have := isAlgClosure_rat L (AlgebraicClosure L)
  have nine := (host_rank_three rank (AlgebraicClosure L) pair).mono
    (by decide : 0 < 2) (by decide : 3 ≤ 9)
  obtain ⟨_, tower⟩ := RiemannReduction.GaussianTower.host_tower_of_rank
    (by decide : 1 ≤ 9) L field nine
  exact ⟨L, inferInstance, inferInstance, twoBase _ q d pair L field, bounds 2 L 9 tower⟩

end RiemannReduction.Mizusawa

namespace RiemannReduction.ConductorOne

theorem rh_of_mizusawa_at_nine (rank : RiemannReduction.Mizusawa.RankThree) :
    RiemannHypothesis := by
  let galois := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let localParameters := UpperTheory.Zero.LLC.recTExists
  let literature : ArchivedInputs.OpenLiteratureStatements := ⟨galois, localParameters, galois⟩
  exact RiemannReduction.WithFrame.RiemannGaussian.AlpogeWindow.rh_of_principal_archived_grid
    Formalism.HN.finite_frame_compat_of (ArchivedInputs.published_results_eigen literature)
    (ArchivedInputs.principal_archived_covolume literature) localParameters
    (supplyChi PChar.one (RiemannReduction.PrincipalLayer.window_from_second_seed
      (RiemannReduction.Mizusawa.nine_input_from_three rank)
      (principal_rankN_inputs literature galois)))

end RiemannReduction.ConductorOne
