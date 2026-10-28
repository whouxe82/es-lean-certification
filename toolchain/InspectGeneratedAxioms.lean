import ES
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx]!
      if modName.getRoot == `ES then
        if info.isAxiom then
          logInfo m!"GENERATED_DECL|{modName}|{name}|unsafe={info.isUnsafe}|type={info.type}"
        if info.isTheorem then
          let axioms ← Lean.collectAxioms name
          logInfo m!"THEOREM_CLOSURE|{modName}|{name}|{axioms}"
          unless axioms.all (fun ax => allowed.contains ax) do
            throwError "unexpected theorem axiom dependency in {name}: {axioms}"
          count := count + 1
  logInfo m!"THEOREM_TOTAL|{count}"
