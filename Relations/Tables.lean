-- таблицы реляционных БД
-- https://lean-lang.org/functional_programming_in_lean/dependent-types/typed-queries.html
-- Таблица Table это список строк Row, построенных по схеме Schema.
-- Схема это список колонок с именем и типом данных DBType.
-- DBType, а также её перевод в типы Lean (asType) являются переменными,
-- т.е. должны задаваться извне (вместе с конкретными схемами, таблицами и пр.).

variable
  (DBType : Type)               -- типы данных БД
  (asType : DBType → Type)      -- их перевод в типы Lean
  [BEq DBType]
  [{t : DBType} → BEq (asType t)]

namespace Tables

-- колонки таблиц
structure Column where
  name : String
  contains : DBType
deriving Repr

-- схема таблицы = список колонок
abbrev Schema := List (Column DBType)

-- строка таблицы, построенная по схеме
abbrev Row : (Schema DBType) → Type
  | [] => Unit
  | [col] => asType col.contains
  | col1 :: col2 :: cols => asType col1.contains × Row (col2::cols)

-- таблица = список строк, построенных по схеме s
abbrev Table (s : (Schema DBType)) := List (Row DBType asType s)

def Row.bEq (r1 r2 : Row DBType asType s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'

instance : BEq (Row DBType asType s) where
  beq := Row.bEq DBType asType

-- "адрес" колонки в схеме
inductive HasCol : (Schema DBType) → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
deriving Repr

def Row.get (row : Row DBType asType s) (col : HasCol DBType s n t) : (asType t) :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next

-- отношение "подсхема"
inductive Subschema : (Schema DBType) → (Schema DBType) → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol DBType bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger

def Subschema.addColumn (sub : Subschema DBType smaller bigger) : Subschema DBType smaller (c :: bigger) :=
  match sub with
  | .nil  => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn

def Subschema.reflexive : (s : Schema DBType) → Subschema DBType s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn

-- проекция строки схемы на строку подсхемы (ограничение)
def Row.project (row : Row DBType asType s) : (s' : Schema DBType) → Subschema DBType s' s → Row DBType asType s'
  | [], .nil => ()
  | [_], .cons c .nil => Row.get DBType asType row c
  | _::_::_, .cons c cs => (Row.get DBType asType row c, row.project _ cs)

-- проверка того, что элементы списков различаются
def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)

-- переименовани колонки по адресу HasCol
def Schema.renameColumn : (s : Schema DBType) → HasCol DBType s n t → String → Schema DBType
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'

end Tables
