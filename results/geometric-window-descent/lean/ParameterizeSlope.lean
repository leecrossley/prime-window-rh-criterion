import Lean
import Lean.Util.FoldConsts

/-! Recheck the part of a proof that uses a given lemma with that lemma
as an explicit parameter. Every produced declaration is added through Lean's kernel.
Constants outside the supplied list retain their original names and proofs. -/
open Lean Meta Elab Command

namespace SlopeReplacement

private def redirect (seed prefixName : Name) (changed : NameSet) (supply : Expr) (e : Expr) : Expr :=
  e.replace fun sub => match sub with
    | .const n ls =>
        if n == seed then some supply
        else if changed.contains n then some (mkApp (.const (prefixName ++ n) ls) supply)
        else none
    | _ => none

private def abstractOne (seed prefixName : Name) (changed : NameSet)
    (seedType : Expr) (ci : ConstantInfo) : MetaM Unit := do
  let n := prefixName ++ ci.name
  let some oldValue := ci.value? (allowOpaque := true)
    | throwError "Expected an existing proof or definition: {ci.name}"
  withLocalDeclD `frameComparison seedType fun supply => do
    let alter := redirect seed prefixName changed supply
    let type ← mkForallFVars #[supply] (alter ci.type)
    let value ← mkLambdaFVars #[supply] (alter oldValue)
    let decl : Declaration ← match ci with
      | .thmInfo v => pure (.thmDecl {name := n, levelParams := v.levelParams, type, value})
      | .defnInfo v =>
        unless v.safety == .safe do throwError "Non-safe definition {ci.name}"
        pure (.defnDecl {name := n, levelParams := v.levelParams, type, value, safety := .safe, hints := v.hints})
      | .opaqueInfo v =>
        if v.isUnsafe then throwError "Unsafe opaque declaration {ci.name}"
        pure (.opaqueDecl {name := n, levelParams := v.levelParams, type, value, isUnsafe := false})
      | _ => throwError "Unsupported declaration kind: {ci.name}"
    addDecl decl

/-- Include the root itself in names. The seed is replaced by the parameter.
Check changed prerequisites before their callers regardless of the input order. -/
def assemble (seed prefixName root : Name) (names : Array Name) : MetaM Unit := do
  let env ← getEnv
  let some seedInfo := env.checked.get.find? seed | throwError "Unknown seed {seed}"
  unless seedInfo.levelParams.isEmpty do throwError "The seed must be monomorphic"
  let mut changed := ({} : NameSet).insert seed
  for n in names do changed := changed.insert n
  unless changed.contains root && root != seed do throwError "Missing root or invalid root"
  let mut work : Array (ConstantInfo × List Name) := #[]
  for n in names do
    unless n == seed do
      let some ci := env.checked.get.find? n | throwError "Missing original declaration {n}"
      let deps := ci.getUsedConstantsAsSet.toList.filter changed.contains
      if deps.isEmpty then throwError "Unrelated declaration {n}"
      work := work.push (ci,deps)
  let mut doneSet := ({} : NameSet).insert seed
  while !work.isEmpty do
    let mut later := #[]
    for (ci,deps) in work do
      if deps.all doneSet.contains then
        abstractOne seed prefixName changed seedInfo.type ci
        doneSet := doneSet.insert ci.name
      else later := later.push (ci,deps)
    if later.size == work.size then throwError "Cyclic or incomplete dependency list: {later.map (fun c => c.1.name)}"
    work := later
  logInfo m!"Checked {doneSet.toList.length-1} declarations with {seed} replaced by a parameter."

/-- Recover the kernel names (including numeric name components) from the modules
listed in the proof reachability report. The final root is audited independently. -/
def readReport (path : System.FilePath) : MetaM (Array Name) := do
  let e ← getEnv
  let contents ← IO.FS.readFile path
  let mut grouped : Std.HashMap String (Std.HashSet String) := {}
  let mut count := 0
  for line in contents.splitOn "\n" do
    unless line.isEmpty do
      match line.splitOn "\t" with
      | [n,_,m,_] =>
          grouped := grouped.insert m ((grouped.getD m {}).insert n)
          count := count+1
      | _ => throwError "Bad report line: {line}"
  let mut actual := #[]
  for i in [:e.allImportedModuleNames.size] do
    if let some wanted := grouped.get? e.allImportedModuleNames[i]!.toString then
      for n in e.header.moduleData[i]!.constNames do
        if wanted.contains n.toString then actual := actual.push n
  unless actual.size == count do throwError "Resolved {actual.size} of {count} report entries"
  return actual

end SlopeReplacement
