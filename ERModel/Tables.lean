-- таблицы реляционных БД
-- https://lean-lang.org/functional_programming_in_lean/dependent-types/typed-queries.html
-- Таблица Table это список строк Row, построенных по схеме Schema.
-- Схема это список колонок с именем и типом данных DBType.
-- DBType, а также её перевод в типы Lean (asType) являются переменными,
-- т.е. должны задаваться извне (вместе с конкретными схемами, таблицами и пр.).

class DBconfig where
  DBType : Type               -- типы данных БД
  asType : DBType → Type      -- их перевод в типы Lean
  -- [{t : DBType} → BEq (asType t)]

section RA
variable
  [DB : DBconfig]
  [{t : DB.DBType} → BEq (DB.asType t)]

namespace RA.Tables

-- колонки таблиц
structure Column where
  name : String
  contains : DB.DBType
-- deriving Repr, BEq

-- схема таблицы = список колонок
abbrev Schema := List Column

-- типы строки таблицы, построенной по схеме (декартово произведение)
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => DB.asType col.contains
  | col :: cols => DB.asType col.contains × Row cols

-- instance : Repr (Row DBType asType s) where
--   reprPrec := fun x _ => match s with
--             | [] => repr ()
--             | [col] => @repr (Repr $ asType col.contains) x
--             | col :: cols => Std.Format.join [(repr col), (repr cols)]

-- таблица = список строк, построенных по схеме s
abbrev Table (s : Schema) := List (Row s)
-- deriving instance Repr for Table

def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'

instance : BEq (Row s) where
  beq := Row.bEq

-- "адрес" колонки в схеме
inductive HasCol : Schema → String → DB.DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
deriving Repr

def Row.get (row : Row s) (col : HasCol s n t) : (DB.asType t) :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next

-- отношение "подсхема"
inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger
deriving Repr

def Subschema.addColumn (sub : Subschema smaller bigger) : Subschema smaller (c :: bigger) :=
  match sub with
  | .nil  => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn

def Subschema.reflexive : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn

-- проекция строки схемы на строку подсхемы (ограничение)
def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => Row.get row c
  | _::_::_, .cons c cs => (Row.get row c, row.project _ cs)

-- проверка того, что элементы списков различаются
def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)

-- переименование колонки по адресу HasCol
def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'

end RA.Tables
