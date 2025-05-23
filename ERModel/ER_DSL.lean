-- ER Model DSL
-- Язык для задания ER-моделей. Правила
import Lean
import ERModel.Relations
import ERModel.ER_DSL_syntax
-- import Lib.Alldecls
open Lean
open Lean.Parser.Term
open Lean.Parser.Command

namespace ER_DSL
-- open Relations

private def mkAtt (acc : TSyntax `command) (b : TSyntax `binding) : MacroM (TSyntax `command) := do
  match b with
  | `(binding| ($is:ident => $ts:term)) =>
    let cmd ← `(command| def $is := $ts)
    `($acc:command
      $cmd:command)
  | _ => Macro.throwError "ER_DSL: mkAtt error"

-- создаём сущность
private def mkEnt (acc : TSyntax `command) (e : TSyntax `entity) : MacroM (TSyntax `command) := do
  match e with
  | `(entity| $nm:ident $[($fld:ident : $fty:ident)]* Items $[($is => $ts)]*) =>
    let nmNam := nm.getId   --(nm.getId.toString ++ "Attrs").toName
    let nmAttrs := mkIdent $ (nmNam.toString ++ "Attrs").toName
    let nmBind := mkIdent $ .str nmNam "attrs"
    -- let nmE := nm.suffix "E"
    let ffty := fty.map (fun (x : TSyntax `ident) => mkIdent $ Name.mkStr2 "Attr" x.getId.toString) -- "bind")
    let cmd ← `(command| structure $nmAttrs where $[($fld:ident : $ffty)]* ) --deriving Repr)
    let mkind ← `(command| inductive $nm : Type where $[| $is:ident]* deriving Repr, BEq)
    -- let op ← `(command| open $(mkIdent $nmNam))
    let mkbind ← `(command| def $nmBind : $nm → $nmAttrs $[| .$is:ident => $ts:term]*)
    -- let mkE ← `(command| abbrev $nmE := ER.mkE $nmIdentBind)
    `($acc:command
      $cmd:command
      $mkind
      open $nm:ident  --$(mkIdent $nmNam:ident)
      $mkbind
      --$mkE
      )
  | _ => Macro.throwError "ER_DSL: mkEnt error"

-- ======  Связи  ======

-- создаём связи
private def mkRel (acc : TSyntax `command) (r : TSyntax `relationship) : MacroM (TSyntax `command) := do
  match r with
  | `(relationship| $e1:ident ($r1:ident) $e2:ident ($r2:ident) $rnam:ident $NN:str
      $[($left:ident → $right:ident)]*) =>
    let proveIsNN ← match NN.getString with
                    | "1N" => `(tactic| proveIs1N)
                    | "N1" => `(tactic| proveIsN1)
                    -- | "NN" => `(tactic| proveIsNN)
                    | "11" => `(tactic| proveIs11)
                    | _ => Macro.throwError "No proof tactic for {NN}"
    let rnamNN := mkIdent (rnam.getId.toString ++ NN.getString).toName
    let Rel := mkIdent `Rel
    let Rel_NN := mkIdent ("Rel_" ++ NN.getString).toName
    let rnamSRel := rnam.suffix "SRel"
    let SRel_NN := mkIdent ("SRel_" ++ NN.getString).toName
    let rnamRelr1 := mkIdent (rnamSRel.getId.toString ++ "." ++ r1.getId.toString).toName
    let rnamRelr2 := mkIdent (rnamSRel.getId.toString ++ "." ++ r2.getId.toString).toName
    let trueid : TSyntaxArray `term := List.toArray $ List.replicate left.size (mkIdent $ Name.mkSimple "True")
    let falseid := mkIdent `False
    let base ← `(def $rnam : $Rel $e1 $e2
                  $[| .$left, .$right => $trueid]*
                  | _,_ => $falseid)
    let NNdef ← `(def $rnamNN : $Rel_NN $e1 $e2 where
                      val := $rnam
                      property := by $proveIsNN:tactic)
    let reldef ←  `(abbrev $rnamSRel := $SRel_NN $rnamNN:ident)
    let roles ← `(def $rnamRelr1 (r : $rnamSRel) : $e1 := r.src
                  def $rnamRelr2 (r : $rnamSRel) : $e2 := r.tgt)
    `($acc:command
      $base:command
      $NNdef:command
      $reldef:command
      $roles:command)
  | _ => Macro.throwError "ER_DSL: mkRel error"

macro_rules
| `(ermodel|
    ERModel $ns:ident where
      Attributes $as*
      Entities $es*
      Relationships $rs*
    endERModel) => do
    let atts ← as.foldlM mkAtt $ TSyntax.mk mkNullNode    -- цикл по атрибутам
    let ents ← es.foldlM mkEnt $ TSyntax.mk mkNullNode    -- цикл по сущностям
    let rels ← rs.foldlM mkRel $ TSyntax.mk mkNullNode    -- цикл по связям
    let nsattr := mkIdent `Attr
    `(namespace $ns:ident
      namespace $nsattr:ident
      $atts:command
      end $nsattr:ident
      $ents:command
      $rels:command
      end $ns:ident)

-- #alldecls
