import Lean
open Lean Elab Command Term Meta

namespace StringType

structure ST0 : Type where
  val : String
  pattern : String := ""
  -- length : Nat := 100
deriving BEq

structure STmin (minLength : Nat): Type extends ST0 where
  minOK : minLength ≤ toST0.val.length := by simp!

structure STmax (maxLength : Nat): Type extends ST0 where
  maxOK : toST0.val.length ≤ maxLength := by simp!

structure STminmax (minLength maxLength : Nat): Type extends ST0 where
  minOK : minLength ≤ toST0.val.length := by simp!
  maxOK : toST0.val.length ≤ maxLength := by simp!

syntax "Str" term* : term
macro_rules
| `(Str $min $max) => `(STminmax $min $max)
| `(Str $min) => `(STmin $min)
| `(Str) => `(ST0)

syntax:max (name:=mystr) "str" term:arg+ : term

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

@[term_elab mystr]
def mystrImpl : TermElab := fun stx typ? => do
  tryPostponeIfNoneOrMVar typ?
  let some typ := typ? | throwError "expected type must be known"
  if typ.isMVar then throwError "expected type must be known"
  let Expr.const base .. := typ.getAppFn | throwError s!"type is not of the expected form: {typ}"
  let [ctor] ← getCtors base | throwError "type {typ} doesn't have exactly one constructor"
  let args := TSyntaxArray.mk stx[1].getArgs
  match ctor with
    | `StringType.ST0.mk => do let stx ← `(ST0.mk $args*)
                               elabTerm stx typ
    | `StringType.STmin.mk => do let stx ← `(STmin.mk (ST0.mk $args*))
                                 elabTerm stx typ
    | `StringType.STminmax.mk => do let stx ← `(STminmax.mk (ST0.mk $args*))
                                   elabTerm stx typ
    | _ => do let stx ← `($(mkIdent ctor) $args*)
              elabTerm stx typ

end StringType
