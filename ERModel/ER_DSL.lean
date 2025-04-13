-- ER Model DSL
-- Язык для задания ER-моделей.
import Lean
import ERModel.ER
-- import Lib.Alldecls
open Lean Elab Meta Syntax
open Lean.Parser.Term
open Lean.Parser.Command

declare_syntax_cat binding
syntax "(" ident " => " term ")" : binding
declare_syntax_cat entity
syntax ident structExplicitBinder* "Items " ident* "Binds " binding* : entity

-- основной синтаксис
syntax "ERModel " ident "where "
  "Attributes " binding*
  "Entities " entity+
  "endERModel" : command

def mkAttrs (is : Array (TSyntax `ident)) (ts : Array (TSyntax `term))
  : MacroM (TSyntax `command) := do
  let attrNam := .mkSimple "Attr"
  let attrId := mkIdent attrNam
  let attrbind := mkIdent $ .str attrNam "bind"
  `(inductive $attrId : Type where $[| $is:ident]*
    deriving Repr
    open $(← `(Lean.Parser.Command.openDecl| $attrId:ident))
    def $attrbind : $attrId → Type $[| .$is:ident => $ts:term]*
    --deriving Repr
    )

def mkEnt (acc : TSyntax `command) (e : TSyntax `entity) : MacroM (TSyntax `command) := do
  match e with
  | `(entity| $nm:ident $[($fld:ident : $fty:ident)]* Items $itm:ident* Binds $[($is => $ts)]*) =>
    let nmNam := Name.mkSimple (nm.getId.toString ++ "Ident")
    let nmIdent := mkIdent nmNam
    let nmIdentBind := mkIdent $ .str nmNam "bind"
    let nmE := mkIdent $ .mkSimple $ nm.getId.toString ++ "E"
    let ffty := fty.map (fun (x : TSyntax `ident) => mkIdent $ Name.mkStr3 "Attr" x.getId.toString "bind")
    let cmd ← `(command| structure $nm where $[($fld:ident : $ffty)]* ) --deriving Repr)
    let mkind ← `(command| inductive $nmIdent : Type where $[| $itm:ident]* deriving Repr)
    let mkbind ← `(command| def $nmIdentBind : $nmIdent → $nm $[| .$is:ident => $ts:term]*
                            -- deriving Repr
                            )
    let mkE ← `(command| abbrev $nmE := ER.mkE $nmIdentBind)
    `($acc:command
      $cmd:command
      $mkind
      $mkbind
      $mkE
      )
            | _ => Macro.throwUnsupported

macro_rules
| `(ERModel $ns:ident where
      Attributes $[($is => $ts)]*
      Entities $es*
    endERModel) => do
    let atts ← mkAttrs is ts
    let ents ← es.foldlM mkEnt $ TSyntax.mk mkNullNode
    `(namespace $ns:ident
      $atts:command
      $ents:command
    end $ns:ident
    )

-- #alldecls
