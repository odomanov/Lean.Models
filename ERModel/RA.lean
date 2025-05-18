-- реляционная алгебра
import ERModel.Tables
open RA.Tables

def List.without [BEq α] (source banned : List α) : List α :=
  source.filter fun r => !(banned.contains r)

section RA
variable
  [DB : DBconfig]
  -- (DBType : Type)
  -- (asType : DBType → Type)
  -- [BEq DBType]
  [{t : DB.DBType} → BEq (DB.asType t)]

namespace RA

-- операции рел.алгебры
inductive Query : Schema → Type where
  | table : Table s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  | select : Query s → (Row s → Bool) → Query s
  | project : Query s → (s' : Schema) → Subschema s' s → Query s'
  | product :
      Query s1 → Query s2 →
      disjoint (s1.map Column.name) (s2.map Column.name) →
      Query (s1 ++ s2)
  | renameColumn :
      Query s → (c : HasCol s n t) → (n' : String) → !((s.map Column.name).contains n') →
        Query (s.renameColumn c n')
  | prefixWith :
      (n : String) → Query s →
      Query (s.map fun c => {c with name := n ++ "." ++ c.name})
-- deriving Repr, BEq

def addVal (v : DB.asType (Column.contains c))
  (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | _ :: _, v' => (v, v')

def Row.append (r1 : Row s1)
  (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, Row.append r' r2)

def Table.cartesianProduct (table1 : Table s1)
  (table2 : Table s2)
  : Table (s1 ++ s2) := Id.run do
  let mut out : Table (s1 ++ s2) := []
  for r1 in table1 do
    for r2 in table2 do
      out := (Row.append r1 r2) :: out
  pure out.reverse

def Row.rename (c : HasCol s n t)
  (row : Row s) :
  Row (Schema.renameColumn s c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal v (Row.rename next r)

def prefixRow (row : Row s)
  : Row (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)

-- исполнение операций Query; результатом является таблица
def Query.exec : Query s → Table s
  | .table t => t
  | .union q1 q2 => exec q1 ++ exec q2
  | .diff q1 q2 => exec q1 |>.without (exec q2)
  | .select q flt => exec q |>.filter flt
  | .project q _ sub => List.map
                        (fun x => (Row.project x _ sub))
                        (exec q)
  | .product q1 q2 _ => Table.cartesianProduct (exec q1) (exec q2)
  | .renameColumn q c _ _ => exec q |>.map (Row.rename c ·)
  | .prefixWith _ q => exec q |>.map (prefixRow)

end RA
