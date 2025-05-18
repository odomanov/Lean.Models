-- DSL для реляционной алгебры. Правила
import Lean
import ERModel.Tables
import ERModel.RA_DSL_syntax
-- import Lib.Alldecls

open Lean
-- open RA.Tables

namespace RA_DSL

private def mkDBTypes (is : Array (TSyntax `ident)) (ts : Array (TSyntax `term))
  : MacroM (TSyntax `command) := do
  let attrNam := .mkSimple "DBType"
  let attrId := mkIdent attrNam
  let attrbind := mkIdent $ .str attrNam "asType"
  `(inductive $attrId : Type where $[| $is:ident]*
    deriving BEq, Repr
    open $(← `(Lean.Parser.Command.openDecl| $attrId:ident))
    def $attrbind : $attrId → Type $[| .$is:ident => $ts:term]*
    instance : DBconfig where
      DBType := $attrId
      asType := $attrbind
    instance {t} : BEq (DBconfig.asType t) where
      beq := match t with
      $[| .$is:ident => @BEq.beq $ts _]*)

private def mkTbl (sch : TSyntax `ident) (acc : TSyntax `command) (tb : TSyntax `table) : MacroM (TSyntax `command) := do
  match tb with
  | `(table| $nm:ident $[{$item:term}]*) =>
    let tblId := mkIdent `Table
    let mktbl ← `(command| def $nm:ident : $tblId $sch:ident := [ $[$item],* ])
    `($acc:command
      $mktbl)
  | _ => Macro.throwError "mkTbl error"

private def mkTablesBlock (acc : TSyntax `command) (st : TSyntax `tablesblock)
  : MacroM (TSyntax `command) := do
  match st with
  | `(tablesblock| Tables $sch:ident $[($f:str : $ty:ident)]* $tb:table*) =>
    let schId := mkIdent `Schema
    let mksch ← `(command| abbrev $sch:ident : $schId:ident := ([ $[⟨$f, $ty⟩],* ] : $schId))
    let mktbls ← tb.foldlM (mkTbl sch) $ TSyntax.mk mkNullNode
    `($acc:command
      $mksch:command
      $mktbls:command)
  | _ => Macro.throwError "mkTablesBlock error"

macro_rules (kind:=ramodel)
| `(ramodel|
    RAModel $ns:ident where
      DBTypes $[($is => $ts)]*
      $st:tablesblock*
    endRAModel) => do
    let types ← mkDBTypes is ts
    let tbls ← st.foldlM mkTablesBlock $ TSyntax.mk mkNullNode
    `(namespace $ns:ident
      $types:command
      $tbls:command
      end $ns:ident)

-- #alldecls
