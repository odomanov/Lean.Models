-- реляционная алгебра
import ERModel.Tables
open RA.Tables

variable
  (DBType : Type)
  (asType : DBType → Type)
  [BEq DBType]
  [{t : DBType} → BEq (asType t)]

namespace RA

-- операции рел.алгебры
inductive Query : Schema DBType → Type where
  | table : Table DBType asType s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  | select : Query s → (Row DBType asType s → Bool) → Query s
  | project : Query s → (s' : Schema DBType) → Subschema DBType s' s → Query s'
  | product :
      Query s1 → Query s2 →
      disjoint (s1.map Column.name) (s2.map Column.name) →
      Query (s1 ++ s2)
  | renameColumn :
      Query s → (c : HasCol DBType s n t) → (n' : String) → !((s.map Column.name).contains n') →
      Query (s.renameColumn DBType c n')
  | prefixWith :
      (n : String) → Query s →
      Query (s.map fun c => {c with name := n ++ "." ++ c.name})
-- deriving Repr, BEq

def addVal (v : asType (Column.contains c))
  (row : Row DBType asType s) : Row DBType asType (c :: s) :=
  match s, row with
  | [], () => v
  | _ :: _, v' => (v, v')

def Row.append (r1 : Row DBType asType s1)
  (r2 : Row DBType asType s2) : Row DBType asType (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal DBType asType v r2
  | _::_::_, (v, r') => (v, Row.append r' r2)

def Table.cartesianProduct (table1 : Table DBType asType s1)
  (table2 : Table DBType asType s2)
  : Table DBType asType (s1 ++ s2) := Id.run do
  let mut out : Table DBType asType (s1 ++ s2) := []
  for r1 in table1 do
    for r2 in table2 do
      out := (Row.append DBType asType r1 r2) :: out
  pure out.reverse

def List.without [BEq α] (source banned : List α) : List α :=
  source.filter fun r => !(banned.contains r)

def Row.rename (c : HasCol DBType s n t)
  (row : Row DBType asType s) :
  Row DBType asType (Schema.renameColumn DBType s c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal DBType asType v (Row.rename next r)

def prefixRow (row : Row DBType asType s)
  : Row DBType asType (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)

-- исполнение операций Query; результатом является таблица
def Query.exec : Query DBType asType s → Table DBType asType s
  | .table t => t
  | .union q1 q2 => exec q1 ++ exec q2
  | .diff q1 q2 => exec q1 |>List.without (exec q2)
  | .select q flt => exec q |>.filter flt
  | .project q _ sub => List.map
                        (fun x => (Row.project DBType asType x _ sub))
                        (exec q)
  | .product q1 q2 _ => Table.cartesianProduct DBType asType (exec q1) (exec q2)
  | .renameColumn q c _ _ => exec q |>.map (Row.rename DBType asType c ·)
  | .prefixWith _ q => exec q |>.map (prefixRow DBType asType)

end RA
