import ES
import Lean.Compiler.IR.CompilerM

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx]!
      if modName.getRoot == `ES && info.isAxiom then
        unless info.isUnsafe do
          throwError "safe project axiom: {name}"
        let hasIR := (Lean.IR.findEnvDecl env name).isSome
        unless hasIR do
          throwError "unsafe axiom lacks compiler IR: {name}"
        count := count + 1
        logInfo m!"STUB_PROVENANCE|{name}|unsafe=true|compiler_IR_present=true"
  logInfo m!"STUB_PROVENANCE_TOTAL|{count}"
