-- ER Model DSL
-- Язык для задания ER-моделей. Синтаксис
import Lean
import ERModel.Common
open Lean.Parser.Command

namespace ER_DSL

-- синт.категории
-- declare_syntax_cat binding
-- scoped syntax "(" ident " => " term ")" : binding
declare_syntax_cat entity
syntax ident structExplicitBinder* "Items " ident* "Binds " binding* : entity
declare_syntax_cat relation
syntax "(" ident " → " ident ")" : relation
declare_syntax_cat relationship
syntax ident "(" ident ")" ident "(" ident ")" ident str relation+ : relationship

-- основной синтаксис
syntax (name := ermodel) "ERModel " ident "where "
  "Attributes " binding+
  "Entities " entity+
  "Relationships" relationship+
  "endERModel" : command
