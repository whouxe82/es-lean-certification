import Mathlib
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if modName.getRoot == `ES then
      logInfo m!"AUDIT_MODULE|{modName}"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx]!
      if modName.getRoot == `ES then
        if info.isAxiom then
          throwError "project declares an axiom: {name}"
        if info.isTheorem then
          let axioms ← Lean.collectAxioms name
          logInfo m!"AUDIT|{modName}|{name}|{axioms}"
          unless axioms.all (fun ax => allowed.contains ax) do
            throwError "unexpected axiom dependency in {name}: {axioms}"
          count := count + 1
  logInfo m!"AUDIT_TOTAL|{count}"
