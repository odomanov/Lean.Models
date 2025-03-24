-- тип Nat с ограничениями
import Lean
open Lean Elab Command Term Meta

namespace NatType

structure Nmin (minValue : Nat): Type where
  val : Nat
  minOK : minValue ≤ val := by simp!  -- автоматический поиск док-ва

structure Nmax (maxValue : Nat): Type where
  val : Nat
  maxOK : val ≤ maxValue := by simp!

structure Nminmax (minValue maxValue : Nat): Type where
  val : Nat
  minOK : minValue ≤ val := by simp!
  maxOK : val ≤ maxValue := by simp!

-- синтаксис для типа
syntax "NatL" term* : term
macro_rules
| `(NatL $min $max) => `(Nminmax $min $max)
| `(NatL $min) => `(Nmin $min)

-- синтаксис для элементов типа
syntax:max (name:=mynat) "nat" term:arg+ : term

private def getCtors (typ : Name) : MetaM (List Name) := do
  let env ← getEnv
  match env.find? typ with
  | some (ConstantInfo.inductInfo val) =>
    pure val.ctors
  | some (ConstantInfo.defnInfo {value:=c,..}) => do
      let Expr.const b .. := c.getAppFn | throwError s!"type is not of the expected form: {c}"
      match (←Lean.getConstInfo b) with
      | (ConstantInfo.inductInfo v) => pure v.ctors
      | _ => pure []
  | _ => pure []

@[term_elab mynat]
def mystrImpl : TermElab := fun stx typ? => do
  tryPostponeIfNoneOrMVar typ?
  let some typ := typ? | throwError "expected type must be known"
  if typ.isMVar then throwError "expected type must be known"
  let Expr.const base .. := typ.getAppFn | throwError s!"type is not of the expected form: {typ}"
  let [ctor] ← getCtors base | throwError "type {typ} doesn't have exactly one constructor"
  let args := TSyntaxArray.mk stx[1].getArgs
  match ctor with
    | `NatType.Nmin.mk => do let stx ← `(Nmin.mk $args*)
                             elabTerm stx typ
    | `NatType.Nminmax.mk => do let stx ← `(Nminmax.mk $args*)
                                elabTerm stx typ
    | _ => do let stx ← `($(mkIdent ctor) $args*)
              elabTerm stx typ

end NatType
