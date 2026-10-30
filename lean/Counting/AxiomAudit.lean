import Lean

/-! A failing, transitive axiom audit, rather than a diagnostic-only printout. -/

open Lean Elab Command

private def allowedAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

private def projectModule (n : Name) : Bool :=
  n.getRoot == `Counting || n.getRoot == `DirectedCountingFormalization

/-- Include private declarations and declarations outside the usual namespaces.
The current module is also audited, including isolated negative-control files. -/
private def projectDeclaration (env : Environment) (projectModules : Array Bool)
    (n : Name) : Bool :=
  n.getRoot == `Counting || n.getRoot == `DirectedCounting ||
    match env.getModuleIdxFor? n with
    | none => true
    | some i => projectModules[i]!

elab "#audit_project" : command => do
  let env ← getEnv
  let projectModules := env.header.moduleNames.map projectModule
  let mut count := 0
  for (name, info) in env.constants.toList do
    if projectDeclaration env projectModules name &&
        (match info with | .axiomInfo _ => true | _ => false) then
      throwError "Forbidden axiom declaration {name} in project source"
    if projectDeclaration env projectModules name &&
        (match info with | .thmInfo _ => true | _ => false) then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowedAxiom axiomName do
          throwError "Forbidden axiom {axiomName} in {name}"
      count := count + 1
  logInfo m!"AXIOM AUDIT PASSED: {count} project theorems; only propext, Classical.choice, Quot.sound permitted."

elab "#audit_declaration " id:ident : command => do
  let n := id.getId
  unless (← getEnv).contains n do
    throwError "Registry declaration does not exist: {n}"
  match (← getEnv).find? n with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Registry declaration is not a proved theorem: {n}"
  for axiomName in ← collectAxioms n do
    unless allowedAxiom axiomName do
      throwError "Forbidden axiom {axiomName} in {n}"

