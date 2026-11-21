import FiniteHundredBlocks
import FiniteFifthBlocks
import Lean.Util.FoldConsts
open Lean Elab Command
private partial def reachable (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: more =>
    if seen.contains n then reachable env more seen else
      let next := (env.checked.get.find? n).map (·.getUsedConstantsAsSet.toList)
      reachable env (next.getD [] ++ more) (seen.insert n)
run_cmd do
  let roots := [``RiemannReduction.DivisorBand.EarlyQuadrature.log_band_error_hundredth,
    ``RiemannReduction.DivisorBand.EarlySmall.small_divisors_cost_five_sixths,
    ``RiemannReduction.DivisorBand.early_deficit_error_explicit,
    ``RiemannReduction.DivisorBand.early_deficit_error_two,
    ``RiemannReduction.DivisorBand.FourthMass.finite_quartic_budget,
    ``RiemannReduction.DivisorBand.FourthMass.finite_hundred_blocks,
    ``RiemannReduction.DivisorBand.FiniteFifth.all_real_of_majorant,
    ``RiemannReduction.DivisorBand.FiniteFifth.integer_and_square_blocks]
  let e ← getEnv
  let used := reachable e roots
  for n in [`sorryAx,`RiemannHypothesis] do
    if used.contains n then throwError "Unexpected dependency {n}"
  for t in roots do
    let ax ← collectAxioms t
    unless ax.all ([`propext,`Classical.choice,`Quot.sound].contains ·) do throwError "Unexpected axioms for {t}: {ax}"
    logInfo m!"{t}: {ax}"
  logInfo m!"Verified {roots.length} roots and {used.toList.length} reachable declarations. No RH dependency."
