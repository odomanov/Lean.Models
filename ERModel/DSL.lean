-- ER Model DSL
import Lean
-- import Lib.Alldecls
open Lean Elab Meta

declare_syntax_cat binding
syntax "(" ident " => " term ")" : binding

syntax "ERModel " ident "where " "Attributes " binding* "endModel" : command

def ERFun (ns : TSyntax `ident) (is : Array (TSyntax `ident)) (ts : Array (TSyntax `term))
  : MacroM (TSyntax `command) := do
  let attrNam := .mkSimple "Attr"
  let attrId := mkIdent attrNam
  let attrbind := mkIdent $ .str attrNam "bind"
  `(namespace $ns:ident
    inductive $attrId : Type where $[| $is:ident]*
    -- open $(← `(Lean.Parser.Command.openDecl| $attrId:ident))
    def $attrbind : $attrId → Type $[| .$is:ident => $ts:term]*
    end $ns:ident
    )
-- #print ERFun

macro_rules
| `(ERModel $ns:ident where Attributes $[($is => $ts)]* endModel) => ERFun ns is ts

-- #alldecls
