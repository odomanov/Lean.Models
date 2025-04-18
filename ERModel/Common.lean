import Lean
open Lean Syntax

declare_syntax_cat binding
syntax "(" ident " => " term ")" : binding

instance : Repr (TSepArray `term ",") where
  reprPrec x _ := repr x.getElems

def Lean.TSyntax.suffix (i : TSyntax `ident) (str : String) : TSyntax `ident :=
  mkIdent (i.getId.toString ++ str).toName
