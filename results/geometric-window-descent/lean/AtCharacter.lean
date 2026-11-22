import Lean

/-! Restrict an archived proof to the one character it actually evaluates.
Lean checks the transformed proof as a new declaration. This works only when
the designated families occur solely at that same character in the proof. -/
open Lean Meta Elab Command

namespace RiemannReduction.CharacterRestriction

def restrictProof (source target : Name) (binderCount selected : Nat)
    (families : Array Nat) : MetaM Unit := do
  let some (.thmInfo theoremInfo) := (← getEnv).checked.get.find? source
    | throwError "Missing source theorem {source}"
  let initial := theoremInfo.value
  let value ← if initial.isLambda then pure initial else whnf initial
  lambdaBoundedTelescope value binderCount fun args body => do
    unless args.size == binderCount && selected < args.size do
      throwError "Wrong binder count for {source}: exposed {args.size}, expected {binderCount}, head {value.getAppFn}, arguments {value.getAppNumArgs}"
    let character := args[selected]!
    let applications := families.map fun i => mkApp args[i]! character
    let mut localTypes := #[]
    for i in [:families.size] do
      let f := args[families[i]!]!
      localTypes := localTypes.push ((← f.fvarId!.getUserName), ← inferType applications[i]!)
    withLocalDeclsDND localTypes fun hypotheses => do
      let restricted := body.replace fun sub =>
        applications.findIdx? (· == sub) |>.map (fun i => hypotheses[i]!)
      let keep := (args.zipIdx.filter fun pair => !families.contains pair.2).map Prod.fst
      let proof ← mkLambdaFVars (keep ++ hypotheses) restricted
      if proof.hasFVar then throwError "A designated family in {source} also occurs away from the selected character"
      let type ← inferType proof
      addDecl (.thmDecl {name := target, levelParams := theoremInfo.levelParams, type, value := proof})
      logInfo m!"Checked {target} at a single character."

/-- Retain the original checked implementation of a helper whose public archive
name includes its source module. Definitions stay reducible through the alias. -/
def nameHelper (moduleName helper target : Name) : MetaM Unit := do
  let source := ((`_private ++ moduleName).num 0) ++ helper
  let info ← getConstInfo source
  let levels := info.levelParams
  let ref := mkConst source (levels.map Level.param)
  match info with
  | .thmInfo _ =>
    addDecl (.thmDecl {name := target, type := info.type, levelParams := levels, value := ref})
  | .defnInfo _ =>
    addDecl (.defnDecl {
      name := target
      type := info.type
      levelParams := levels
      value := ref
      hints := .abbrev
      safety := .safe })
    setReducibilityStatus target .reducible
  | _ => throwError "Unsupported kind of archive helper {source}"

end RiemannReduction.CharacterRestriction
