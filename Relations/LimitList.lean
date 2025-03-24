-- Список ограниченной длины
import Lean
open Lean Elab Command Term Meta

namespace LimitList

-- список без верхнего предела
structure LimListL (α : Type u) (lower : Nat) where
  list : List α
  lower_le : lower ≤ list.length := by simp -- док-во, что lower не больше длины списка

-- список с (дополнительным) верхним пределом
structure LimListU (α : Type u) (lower upper : Nat) extends LimListL α lower where
  le_upper : list.length ≤ upper := by simp
  lower_le_upper : lower ≤ upper := by simp  -- док-во, что lower не больше upper

-- синтаксис для типов
-- ⋆ означает отсутствие верхнего предела
syntax "LimList" term+ "⋆"? : term
macro_rules
  | `(term|LimList $t $l $u) => `(LimListU $t $l $u)
  | `(term|LimList $t $l ⋆)  => `(LimListL $t $l)

-- синтаксис для элементов типов
syntax (name:=limlist) "⟦" term,* "⟧" : term

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

@[term_elab limlist]
def limlistImpl : TermElab := fun stx typ? => do
  tryPostponeIfNoneOrMVar typ?
  let some typ := typ? | throwError "expected type must be known"
  if typ.isMVar then throwError "expected type must be known"
  let Expr.const base .. := typ.getAppFn | throwError s!"type is not of the expected form: {typ}"
  let [ctor] ← getCtors base | throwError "type {typ} doesn't have exactly one constructor"
  let args := TSyntaxArray.mk stx[1].getSepArgs
  match ctor with
    | `LimitList.LimListL.mk => do let stx ← `(LimListL.mk [$args,*])
                                   elabTerm stx typ
    | `LimitList.LimListU.mk => do let stx ← `(LimListU.mk (LimListL.mk [$args,*]))
                                   elabTerm stx typ
    | _ => do let stx ← `($(mkIdent ctor) $args*)
              elabTerm stx typ


end LimitList
