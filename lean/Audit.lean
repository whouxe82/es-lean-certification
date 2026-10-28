import ES
import Lean.Util.CollectAxioms

-- Resource limit for environment inspection only; kernel checking stays enabled.
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut theoremCount := 0
  let mut safeCount := 0
  let mut stubCount := 0
  for modName in env.header.moduleNames do
    if modName.getRoot == `ES then
      logInfo m!"AUDIT_MODULE|{modName}"
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx]!
      if modName.getRoot == `ES then
        if info.isAxiom then
          -- Lean's compiler serializes unsafe computational specializations as
          -- axiom-info entries. They are inventoried, never whitelisted as
          -- logical dependencies. Authored axiom commands are separately banned.
          unless info.isUnsafe do
            throwError "project declares a safe mathematical axiom: {name}"
          logInfo m!"AUDIT_COMPILER_STUB|{modName}|{name}|unsafe={info.isUnsafe}|type={info.type}"
          stubCount := stubCount + 1
        else if !info.isUnsafe then
          let axioms ← Lean.collectAxioms name
          unless axioms.all (fun ax => allowed.contains ax) do
            throwError "unexpected axiom dependency in {name}: {axioms}"
          if info.isTheorem then
            logInfo m!"AUDIT|{modName}|{name}|{axioms}"
            theoremCount := theoremCount + 1
          else
            logInfo m!"AUDIT_SAFE_DECL|{modName}|{name}|{axioms}"
            safeCount := safeCount + 1
  logInfo m!"AUDIT_SAFE_TOTAL|{safeCount}"
  logInfo m!"AUDIT_COMPILER_STUB_TOTAL|{stubCount}"
  logInfo m!"AUDIT_TOTAL|{theoremCount}"
