module

import Lean
import all Lean.Util.CollectAxioms

open Lean

private def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Audit the declarations made by the requested modules, including private declarations.
Follow their types and proof terms across imports to find their transitive axioms. -/
public def main (args : List String) : IO UInt32 := do
  let modules := args.toArray.map String.toName
  if modules.isEmpty then
    throw (IO.userError "No modules to audit")
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map fun name => { module := name }) {}
  let moduleNames := env.allImportedModuleNames
  let declarations := env.constants.fold (init := #[]) fun names decl _ =>
    if let some i := env.getModuleIdxFor? decl then
      if modules.contains moduleNames[i.toNat]! then names.push decl else names
    else
      names
  if declarations.isEmpty then
    throw (IO.userError "No project declarations to audit")
  -- Keep one traversal cache and read the proof terms from the private environment.
  let violations := CollectAxioms.runM env do
    let mut violations := #[]
    for decl in declarations do
      let axioms ← CollectAxioms.collectAndGet (fun _ _ => none) decl
      let forbidden := axioms.filter (!allowedAxioms.contains ·)
      unless forbidden.isEmpty do
        violations := violations.push (decl.toString, forbidden.toList.map Name.toString)
    return violations
  for (decl, axioms) in violations.qsort (fun a b => a.1 < b.1) do
    IO.eprintln s!"{decl} depends on forbidden axioms: {String.intercalate ", " axioms}"
  if !violations.isEmpty then
    return 1
  IO.println s!"Audited {declarations.size} declarations in {modules.size} modules."
  return 0
