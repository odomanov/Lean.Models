-- список всех определений в модуле
import Lean
import Batteries

open Lean Elab Command

elab "#alldecls" : command => do
  let decls ← liftCoreM Batteries.Tactic.Lint.getDeclsInCurrModule
  logInfo s!"{decls.filter fun name ↦ ¬ (name.isInternal)}"
