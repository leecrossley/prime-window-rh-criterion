import CheckAlpogePrincipalArchivedGeometryRH
import AuditSlopeGraph

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannGaussian.AlpogeWindow.rh_of_principal_archived_geometry
    [`UpperTheory.V.Cu.main4_alt, `UpperTheory.V.Two.baseRk]
    [] true (some "published-rh-names.txt")
