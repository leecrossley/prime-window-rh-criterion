import FourthSignedCriterion
import Lean.Util.FoldConsts
open Lean Elab Command

private partial def proofDependencies (env : Environment) (pending : List Name) (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then proofDependencies env rest seen else
      let used := (env.checked.get.find? n).map (·.getUsedConstantsAsSet.toList)
      proofDependencies env (used.getD [] ++ rest) (seen.insert n)

run_cmd do
  let env ← getEnv
  let ns := `RiemannReduction.DivisorBand
  let fm := ns ++ `FourthMass
  let roots := [ns ++ `fourth_power_interval, ns ++ `fourth_sample_excursions] ++
    [`signed_mass_discrepancy, `quartic_mass_grows, `rh_iff_signed_quartic_budget, `remainder_mass_grows,
     `rh_iff_subpower_quartic_budget, `all_squares_of_quartic_loss, `all_squares_of_subpower_quartic_loss].map (fm ++ ·)
  for n in roots do
    let ax ← collectAxioms n
    unless ax.all ([`propext, `Classical.choice, `Quot.sound].contains ·) do throwError "Unexpected axioms at {n}: {ax}"
    logInfo m!"{n}: {ax}"
  let allNames := proofDependencies env roots
  for n in [`sorryAx, `riemannHypothesis,`UpperTheory.FinalTheorems.riemannHypothesis,
            `RiemannReduction.ConductorOne.rh_of_dyadic_principal_window,
            `RiemannGaussian.AlpogeWindow.rh_of_principal_archived_geometry] do
    if allNames.contains n then throwError "Unexpected dependency {n}"
  for n in allNames do
    if let some (.thmInfo t) := env.checked.get.find? n then
      if t.type == .const `RiemannHypothesis [] then throwError "Reachable theorem {n} has the literal type RiemannHypothesis"
  for n in [ns ++ `tenth_signed_peaks, ns ++ `tenth_peak_height, ns ++ `deficit_pair_error_two,
      ns ++ `square_root_bound_of_rh, ns ++ `unpairedTail, fm ++ `mass] do
    unless allNames.contains n do throwError "Missing expected dependency {n}"
  let pure := proofDependencies env [fm ++ `signed_mass_discrepancy]
  if pure.contains `RiemannHypothesis then throwError "RH in arithmetic discrepancy"
  logInfo m!"Verified {roots.length} signed criterion and sampling statements with {allNames.toList.length} reachable declarations. None of the reachable theorems has the literal type RiemannHypothesis."
