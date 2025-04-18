-- DSL для реляционной алгебры. Синтаксис
import Lean
import ERModel.Common

namespace RA_DSL

-- declare_syntax_cat binding
-- scoped syntax "(" ident " => " term ")" : binding
declare_syntax_cat schrow
syntax "(" str " : " ident ")" : schrow
declare_syntax_cat schema
syntax ident schrow* : schema
declare_syntax_cat table
syntax ident ("{" term "}")* : table
declare_syntax_cat tablesblock
syntax "Tables " schema table* : tablesblock

syntax (name:=ramodel)  "RAModel " ident "where"
  "DBTypes" binding*
  tablesblock*
  "endRAModel" : command
