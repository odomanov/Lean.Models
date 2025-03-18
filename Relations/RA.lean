-- реляционная алгебра
import Relations.Tables

variable
  (DBType : Type)
  (asType : DBType → Type)
  [BEq DBType]
  [{t : DBType} → BEq (asType t)]
  -- (Schema : Type → Type)
  -- (DBExpr : Tables.Schema DBType → DBType → Type)
  -- (evaluate0 : {s : Schema DBType} {t : DBType} → DBExpr s t → asType t)
  -- (evaluate0 : {t : DBType} → {s : Tables.Schema DBType}
  --   → (row : Tables.Row DBType asType s) → DBExpr s t → (asType t))
  -- [{s : Tables.Schema DBType} → {t : DBType} → Repr (DBExpr s t)]

namespace RA

inductive Query : Tables.Schema DBType → Type where
  | table : Tables.Table DBType asType s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  -- | select : Query s → DBExpr s .bool → Query s
  | select : Query s → (Tables.Row DBType asType s → Bool) → Query s
  -- | select : Query s → DBExpr s t → (_ : asType t = Bool) → Query s
  | project : Query s → (s' : Tables.Schema DBType) → Tables.Subschema DBType s' s → Query s'
  | product :
      Query s1 → Query s2 →
      Tables.disjoint (s1.map Tables.Column.name) (s2.map Tables.Column.name) →
      Query (s1 ++ s2)
  | renameColumn :
      Query s → (c : Tables.HasCol DBType s n t) → (n' : String) → !((s.map Tables.Column.name).contains n') →
      Query (s.renameColumn DBType c n')
  | prefixWith :
      (n : String) → Query s →
      Query (s.map fun c => {c with name := n ++ "." ++ c.name})

def addVal (v : asType (Tables.Column.contains c))
  (row : Tables.Row DBType asType s) : Tables.Row DBType asType (c :: s) :=
  match s, row with
  | [], () => v
  | _ :: _, v' => (v, v')

def Tables.Row.append (r1 : Tables.Row DBType asType s1)
  (r2 : Tables.Row DBType asType s2) : Tables.Row DBType asType (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal DBType asType v r2
  | _::_::_, (v, r') => (v, Tables.Row.append r' r2)

-- -- def List.flatMap (f : α → List β) : (xs : List α) → List β
-- --   | [] => []
-- --   | x :: xs => f x ++ xs.flatMap f

-- -- def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) : Table (s1 ++ s2) :=
-- --   table1.flatMap fun r1 => table2.map r1.append

def Tables.Table.cartesianProduct (table1 : Tables.Table DBType asType s1)
  (table2 : Tables.Table DBType asType s2)
  : Tables.Table DBType asType (s1 ++ s2) := Id.run do
  let mut out : Tables.Table DBType asType (s1 ++ s2) := []
  for r1 in table1 do
    for r2 in table2 do
      out := (Tables.Row.append DBType asType r1 r2) :: out
  pure out.reverse

def List.without [BEq α] (source banned : List α) : List α :=
  source.filter fun r => !(banned.contains r)

def Tables.Row.rename (c : Tables.HasCol DBType s n t)
  (row : Tables.Row DBType asType s) :
  Tables.Row DBType asType (Tables.Schema.renameColumn DBType s c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal DBType asType v (Tables.Row.rename next r)

def prefixRow (row : Tables.Row DBType asType s)
  : Tables.Row DBType asType (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)

def Query.exec : Query DBType asType s → Tables.Table DBType asType s
  | .table t => t
  | .union q1 q2 => exec q1 ++ exec q2
  | .diff q1 q2 => exec q1 |>List.without (exec q2)
  | .select q flt => exec q |>.filter flt
  -- | .select q e isb => List.filter e
  --                      (fun r => isb ▸ (evaluate0 r e))
  --                      (exec q)
  -- | .project q _ sub => List.map (Tables.Row.project DBType asType sub _ ·) (exec q)
  | .project q _ sub => List.map
                        (fun x => (Tables.Row.project DBType asType x _ sub))
                        (exec q)
  | .product q1 q2 _ => Tables.Table.cartesianProduct DBType asType (exec q1) (exec q2)
  | .renameColumn q c _ _ => exec q |>.map (Tables.Row.rename DBType asType c ·)
  | .prefixWith _ q => exec q |>.map (prefixRow DBType asType)

end RA
