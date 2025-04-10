-- ER Model DSL
-- Язык для задания ER-моделей.
import Lean
-- import Lib.Alldecls
open Lean Elab Meta Syntax
open Lean.Parser.Term
open Lean.Parser.Command

declare_syntax_cat binding
syntax "(" ident " => " term ")" : binding
declare_syntax_cat entity
syntax ident structExplicitBinder* : entity

-- основной синтаксис
syntax "ERModel " ident "where "
  "Attributes " binding*
  "Entities " entity+
  "endModel" : command

def mkAttrs (is : Array (TSyntax `ident)) (ts : Array (TSyntax `term))
  : MacroM (TSyntax `command) := do
  let attrNam := .mkSimple "Attr"
  let attrId := mkIdent attrNam
  let attrbind := mkIdent $ .str attrNam "bind"
  `(inductive $attrId : Type where $[| $is:ident]*
    open $(← `(Lean.Parser.Command.openDecl| $attrId:ident))
    def $attrbind : $attrId → Type $[| .$is:ident => $ts:term]*
    )

def mkEnts (ents : List $ TSyntax `entity) : MacroM (TSyntax `command) := do
  match ents with
  | [] => Macro.throwError "empty entities list"
  | [e] => do
          -- dbg_trace "[e]={e.raw}"
          match e.raw  with
           | `(entity| $nm:ident $flds:structExplicitBinder*) =>
              -- dbg_trace "ENT={nm}\n>> {flds}"
              `(structure $nm where
                  $flds:structExplicitBinder*
              )
            | _ => Macro.throwUnsupported
  | e::rest => do
          -- dbg_trace "[e::rest]={e.raw}"
           match e.raw with
           | `(entity| $nm:ident $flds:structExplicitBinder*) =>
              -- dbg_trace "ENT={nm}> \nREST={rest}"
              let rst ← mkEnts rest
              `(
                structure $nm:ident where
                  $flds:structExplicitBinder*
                $rst:command
              )
            | _ => Macro.throwUnsupported

macro_rules
| `(ERModel $ns:ident where
      Attributes $[($is => $ts)]*
      Entities $es*
    endModel) => do
    let atts ← mkAttrs is ts
    let ents ← mkEnts es.toList
    `(namespace $ns:ident
      $atts:command
      $ents:command
    end $ns:ident
    )

-- #alldecls

-- structure Department where
--   name : str.bind

-- structure Employee where
--   emp_no : emp_no.bind
--   name   : name.bind
--   age    : age.bind

-- structure Project where
--   proj_no : num.bind

-- -- тип, собирающий все сущности
-- inductive Entity where
-- | dep (d : Department)
-- | emp (e : Employee)
-- | prj (p : Project)
