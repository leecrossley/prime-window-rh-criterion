import PrincipalArchivedInputs
import PrincipalArchivedWindow
import FiniteGeometricFrame
import ParameterizeSlope

/-! The comparison from Hermitian lattices is supplied explicitly throughout the
sixteen theorems that carry it to the principal-character grid. Each original
proof body is checked again with that argument. The theorem in SecondSeedRH
uses finite rank tests and retains Alpöge's theta-chain construction and
Sanftenberg's reduction to the principal character. -/

open Lean Elab Command in
run_cmd liftTermElabM do
  SlopeReplacement.assemble `Formalism.HN.theoremFSharp_of `RiemannReduction.WithFrame
    `RiemannGaussian.AlpogeWindow.rh_of_principal_archived_grid
    #[`Formalism.HN.frame_theorem_sharp,
      `Formalism.HN.frame_theorem_log_ideal,
      `Formalism.HN.theoremFSharp,
      `Formalism.HN.theoremF,
      `Formalism.LFunctionChainParameters.MatrixLatticeEstimates.flat_lattice_theorem_holds,
      `Formalism.LFunctionChainParameters.MatrixLatticeEstimates.sharp_flat_lattice_theorem_holds,
      `Formalism.LFunctionChainParameters.MatrixLatticeEstimates.ramification_condition_holds,
      `Formalism.LFunctionChainParameters.MatrixLatticeEstimates.joint_a_ramified_holds,
      `Formalism.MainNotions.Lnk.frame_at_of,
      `Formalism.MainNotions.Lnk.frameF_of,
      `RiemannGaussian.AlpogeWindow.principal_frame_of_forms,
      `RiemannGaussian.AlpogeWindow.rh_of_principal_selected_geometry,
      `RiemannGaussian.AlpogeWindow.rh_of_principal_archived_bundle_choices,
      `RiemannGaussian.AlpogeWindow.rh_of_principal_archived_bundle_rows,
      `RiemannGaussian.AlpogeWindow.rh_of_principal_archived_open_rows,
      `RiemannGaussian.AlpogeWindow.rh_of_principal_archived_grid]
