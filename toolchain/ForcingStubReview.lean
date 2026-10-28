import ES
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut thms := 0
  let mut safeDefs := 0
  let mut stubs := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx]!
      if modName.getRoot == `ES then
        if info.isAxiom then
          stubs := stubs + 1
          logInfo m!"AXIOM_DECL|{modName}|{name}|unsafe={info.isUnsafe}|type={info.type}"
        if info.isTheorem || (!info.isUnsafe && !info.isAxiom) then
          let axioms ← Lean.collectAxioms name
          unless axioms.all (fun ax => allowed.contains ax) do
            throwError "unexpected dependency: {name}: {axioms}"
          if info.isTheorem then
            thms := thms + 1
          else
            safeDefs := safeDefs + 1
  logInfo m!"REVIEW_TOTAL|theorems={thms}|other_safe_declarations={safeDefs}|axiom_stubs={stubs}|all_dependency_closures_whitelisted=true"
