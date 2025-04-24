-- ER Model DSL
-- Язык для задания ER-моделей. Правила
import Lean
import ERModel.ER
import ERModel.ER_DSL_syntax
-- import Lib.Alldecls
open Lean
open Lean.Parser.Term
open Lean.Parser.Command

namespace ER_DSL

-- создаём тип атрибутов Attr и функцию Attr.bind
private def mkAttrs (is : Array (TSyntax `ident)) (ts : Array (TSyntax `term))
  : MacroM (TSyntax `command) := do
  let attrNam := `Attr
  let attrId := mkIdent attrNam
  let attrbind := mkIdent $ .str attrNam "bind"
  `(inductive $attrId : Type where $[| $is:ident]*
    deriving Repr, BEq
    open $(← `(Lean.Parser.Command.openDecl| $attrId:ident))        -- open Attr
    def $attrbind : $attrId → Type $[| .$is:ident => $ts:term]*)

-- создаём сущность
private def mkEnt (acc : TSyntax `command) (e : TSyntax `entity) : MacroM (TSyntax `command) := do
  match e with
  | `(entity| $nm:ident $[($fld:ident : $fty:ident)]* Items $[($is => $ts)]*) =>
    let nmNam := (nm.getId.toString ++ "Ident").toName
    let nmIdent := mkIdent nmNam
    let nmIdentBind := mkIdent $ .str nmNam "bind"
    let nmE := nm.suffix "E"
    let ffty := fty.map (fun (x : TSyntax `ident) => mkIdent $ Name.mkStr3 "Attr" x.getId.toString "bind")
    let cmd ← `(command| structure $nm where $[($fld:ident : $ffty)]* ) --deriving Repr)
    let mkind ← `(command| inductive $nmIdent : Type where $[| $is:ident]* deriving Repr, BEq)
    let mkbind ← `(command| def $nmIdentBind : $nmIdent → $nm $[| .$is:ident => $ts:term]*)
    let mkE ← `(command| abbrev $nmE := ER.mkE $nmIdentBind)
    `($acc:command
      $cmd:command
      $mkind
      $mkbind
      $mkE)
  | _ => Macro.throwError "ER_DSL: mkEnt error"

-- ======  Связи  ======

-- тактики для доказательства условий на отношения 1:N, 1:1
syntax "proveIs1N" : tactic
macro_rules
| `(tactic| proveIs1N) =>
  `(tactic|
    intros a b c; intros;
    cases a <;> cases b <;> cases c <;> simp <;> contradiction)
syntax "proveIs11" : tactic
macro_rules
| `(tactic| proveIs11) =>
  `(tactic|
    intros a b c d; intros;
    cases a <;> cases b <;> cases c <;> cases d <;> simp <;> contradiction)

-- создаём связи
private def mkRel (acc : TSyntax `command) (r : TSyntax `relationship) : MacroM (TSyntax `command) := do
  match r with
  | `(relationship| $e1:ident ($r1:ident) $e2:ident ($r2:ident) $rnam:ident $NN:str
      $[($left:ident → $right:ident)]*) =>
    let rnamIdent := rnam.suffix "Ident"
    let rnamIdentBase := rnamIdent.suffix "Base"
    let e1Ident := e1.suffix "Ident"
    let e2Ident := e2.suffix "Ident"
    let e1Identbind := mkIdent $ .str e1Ident.getId "bind"
    let e2Identbind := mkIdent $ .str e2Ident.getId "bind"
    let proveIsNN ← match NN.getString with
                    | "1N" => `(tactic| proveIs1N)
                    | "11" => `(tactic| proveIs11)
                    | _ => Macro.throwError "No proof tactic for {NN}"
    let rnamIdentNN := mkIdent (rnamIdent.getId.toString ++ NN.getString).toName
    let rnamIdentNNbind := mkIdent $ .str rnamIdentNN.getId "bind"
    let REL := mkIdent `REL
    let REL_NN := mkIdent ("REL_" ++ NN.getString).toName
    let REL_NNbind := mkIdent $ .str REL_NN.getId "bind"
    let rnamIdentRel := mkIdent (rnamIdent.getId.toString ++ "Rel").toName
    let rnamRel := rnam.suffix "Rel"
    let Relbind := mkIdent `Rel.bind
    let Rel_NN := mkIdent ("Rel_" ++ NN.getString).toName
    let rnamRelbind := mkIdent $ .str rnamRel.getId "bind"
    let rnamIdentRelr1 := mkIdent (rnamIdentRel.getId.toString ++ "." ++ r1.getId.toString).toName
    let rnamIdentRelr2 := mkIdent (rnamIdentRel.getId.toString ++ "." ++ r2.getId.toString).toName
    let rnamRelr1 := mkIdent (rnamRel.getId.toString ++ "." ++ r1.getId.toString).toName
    let rnamRelr2 := mkIdent (rnamRel.getId.toString ++ "." ++ r2.getId.toString).toName
    let trueid : TSyntaxArray `term := List.toArray $ List.replicate left.size (mkIdent $ Name.mkSimple "True")
    let falseid := mkIdent `False
    let e1E := e1.suffix "E"
    let e2E := e2.suffix "E"
    let base ← `(def $rnamIdentBase : $REL $e1Ident $e2Ident
                  $[| .$left, .$right => $trueid]*
                  | _,_ => $falseid)
    let NNdef ← `(def $rnamIdentNN : $REL_NN $e1Ident $e2Ident where
                      pred := $rnamIdentBase
                      cond := by $proveIsNN:tactic)
    let NNdef2 ← `(def $rnamIdentNNbind := $REL_NNbind $e1Identbind $e2Identbind)
    let reldef ←  `(abbrev $rnamIdentRel := $Rel_NN $rnamIdentNN:ident
                    abbrev $rnamRel := $Rel_NN ($REL_NNbind $e1Identbind $e2Identbind $rnamIdentNN)
                    def $rnamRelbind := $Relbind $e1Identbind $e2Identbind
                      $(mkIdent (.str rnamIdentNN.getId "pred")))
    let roles ← `(def $rnamIdentRelr1 (r : $rnamIdentRel) : $e1Ident := r.src
                  def $rnamIdentRelr2 (r : $rnamIdentRel) : $e2Ident   := r.tgt
                  def $rnamRelr1 (r : $rnamRel) : $e1E := r.src
                  def $rnamRelr2 (r : $rnamRel) : $e2E := r.tgt)
    `($acc:command
      $base:command
      $NNdef:command
      $NNdef2:command
      $reldef:command
      $roles:command)
  | _ => Macro.throwError "ER_DSL: mkRel error"

macro_rules
| `(ermodel|
    ERModel $ns:ident where
      Attributes $[($is => $ts)]*
      Entities $es*
      Relationships $rs*
    endERModel) => do
    let atts ← mkAttrs is ts
    let ents ← es.foldlM mkEnt $ TSyntax.mk mkNullNode    -- цикл по сущностям
    let rels ← rs.foldlM mkRel $ TSyntax.mk mkNullNode    -- цикл по связям
    `(namespace $ns:ident
      $atts:command
      $ents:command
      $rels:command
      end $ns:ident)

-- #alldecls
