import Lean
import Lean.Util.FoldConsts

open Lean Elab Command
namespace FiniteFrameAudit

/-- The same references as ConstantInfo.getUsedConstantsAsSet, collected into
one global hash set during the traversal. Duplicates in a work list do not
alter reachability. -/
private def dependencies (c : ConstantInfo) : List Name :=
  let inType := c.type.getUsedConstants.toList
  inType ++ match c.value? (allowOpaque := true) with
    | some v => v.getUsedConstants.toList
    | none => match c with
      | .inductInfo n => n.ctors
      | .ctorInfo n => [n.name]
      | .recInfo n => n.all
      | _ => []

private partial def visit (e : Lean.Kernel.Environment) (work : List Name)
    (seen : Std.HashSet Name := {}) : Std.HashSet Name :=
  match work with
  | [] => seen
  | n::ns =>
    if seen.contains n then visit e ns seen else
      let more := (e.find? n).map dependencies
      visit e (more.getD [] ++ ns) (seen.insert n)

def verify (root : Name) (need avoid : List Name) (bareRH : Bool)
    (dump : Option System.FilePath := none) : CommandElabM Unit := do
  let e := (← getEnv).checked.get
  let some (.thmInfo d) := e.find? root | throwError "Missing theorem {root}"
  if bareRH && d.type != .const `RiemannHypothesis [] then throwError "Wrong endpoint type: {d.type}"
  let ax ← collectAxioms root
  unless ax.all ([`propext,`Classical.choice,`Quot.sound].contains ·) do throwError "Nonstandard axioms: {ax}"
  let reachable := visit e [root]
  for n in need do
    unless reachable.contains n do throwError "Missing expected dependency {n}"
  for n in `sorryAx::avoid do
    if reachable.contains n then throwError "Unwanted dependency {n}"
  let mut otherRH := #[]
  let file ← dump.mapM (fun path => IO.FS.Handle.mk path .write)
  for n in reachable do
    if let some f := file then f.putStrLn n.toString
    if n != root then
      if let some (.thmInfo th) := e.find? n then
        if th.type == .const `RiemannHypothesis [] then otherRH := otherRH.push n
  if let some f := file then f.flush
  unless otherRH.isEmpty do throwError "Other closed RH theorems used: {otherRH}"
  logInfo m!"{root}: {reachable.size} reachable declarations; axioms {ax}; no previously closed RH theorem."
  for n in [`Formalism.HN.thmF_share,`Formalism.HN.frameB_integral,`Formalism.CorankShareLayerCake.FR.layer_cake_formula,
      `IntegratedSlopeShare.shortfall_integral,`IntegratedSlopeShare.rank_share_transfer] do
    logInfo m!"Reachability of {n}: {reachable.contains n}"

end FiniteFrameAudit
