import BalancedCutoffs
import Lean.Util.FoldConsts

open Lean Elab Command

private partial def usedBy (env : Environment) (pending : List Name) (seen : NameSet := {}) :
    NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n then usedBy env rest seen
    else
      let deps := (env.checked.get.find? n).map (·.getUsedConstantsAsSet.toList)
      usedBy env (deps.getD [] ++ rest) (seen.insert n)

run_cmd do
  let env ← getEnv
  let roots := [``RiemannReduction.BalancedCutoffs.positive_reweight,
    ``RiemannReduction.BalancedCutoffs.arithmetic_prefix_probabilities,
    ``RiemannReduction.BalancedCutoffs.relative_defect, ``RiemannReduction.BalancedCutoffs.gain_loss,
    ``RiemannReduction.BalancedCutoffs.log_prefix_derivative,
    ``RiemannReduction.CutoffVariation.shift_integral,
    ``RiemannReduction.CutoffVariation.threshold_integral,
    ``RiemannReduction.CutoffVariation.component_width]
  for n in roots do
    let ax ← collectAxioms n
    unless ax.all ([`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "Unexpected axioms at {n}: {ax}"
  let used := usedBy env roots
  for n in [`sorryAx, `RiemannHypothesis] do
    if used.contains n then throwError "Unexpected dependency {n}"
  logInfo m!"Checked {roots.length} cutoff components with {used.toList.length} reachable declarations."
