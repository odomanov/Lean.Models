-- ER Model DSL
-- Язык для задания ER-моделей.
import Lean
import ERModel.RA
import ERModel.RA_DSL
-- import Lib.Alldecls
open Lean Elab Meta Syntax
open Lean.Parser.Term
open Lean.Parser.Command
set_option linter.unusedVariables false

declare_syntax_cat erbinding
syntax "(" ident " => " "⟨" term,+ "⟩" ")" : erbinding
declare_syntax_cat entity
syntax ident structExplicitBinder* "Items " ident* "Binds " erbinding* : entity

-- основной синтаксис
syntax "ERModel " ident "where "
  "Attributes " binding+
  "Entities " entity+
  "endERModel" : command

def mkTbl2 (acc : TSyntaxArray `tblrow) (tb : TSyntax `erbinding) : MacroM (TSyntaxArray `tblrow) := do
  match tb with
  | `(erbinding| ($id:ident => ⟨ $val,* ⟩)) =>
    match val.getElems with
    | #[v] => do
        let (vv : TSyntax `term) := ⟨v⟩
        let line ← `(tblrow| {($vv:term)})
        let acc := acc.push line
        pure acc
    | v => do
        let vrest := v.extract 1
        let v1 := v[0]!
        let ins ← `(tuple| ($v1, $vrest,*))
        let line ← `(tblrow| {$ins:tuple})
        let acc := acc.push line
        pure acc
  | _ => Macro.throwError "mkTbl2 error"

def mkEnt (acc : TSyntaxArray `tablesblock) (e : TSyntax `entity) : MacroM (TSyntaxArray `tablesblock) := do
  match e with
  | `(entity| $nm:ident $[($fld:ident : $fty:ident)]* Items $itm:ident* Binds $bnds*) => --$[($id:ident => ⟨ $val:term,* ⟩)]*) =>
    let schId := mkIdent $ Name.mkStr1 $ "Schema".append nm.getId.toString
    let fldstr := fld.map (fun x => TSyntax.mk (mkStrLit x.getId.toString))
    let mksch ← `(schema| $schId:ident $[($fldstr : $fty)]*)
    let mktbls ← bnds.foldlM mkTbl2 $ #[]
    let tbbb := #[← `(table| $nm:ident $mktbls:tblrow*)]
    let schtbl ← `(tablesblock| Tables $mksch:schema $tbbb:table*)
    let acc := acc.push schtbl
    pure acc
  | _ => Macro.throwError "mkEnt error"

macro_rules
| `(ERModel $ns:ident where
      Attributes $bnd:binding*
      Entities $es*
    endERModel) => do
    let schtbls ← es.foldlM mkEnt $ #[]
    `(ramodel|
      RAModel $ns:ident where
      DBTypes $bnd:binding*
      $schtbls:tablesblock*
      endRAModel)

-- #alldecls
