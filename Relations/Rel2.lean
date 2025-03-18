import Relations.Tables
import Relations.Rel1
import Relations.RA

abbrev Row.get : Row s → HasCol s n t→ (asType t) :=
  Tables.Row.get DBType asType

inductive DBExpr (s : Schema) : DBType → Type where
  | col (n : String) (loc : Tables.HasCol DBType s n t) : DBExpr s t
  | eq (e1 e2 : DBExpr s t) : DBExpr s .bool
  | lt (e1 e2 : DBExpr s .int) : DBExpr s .bool
  | and (e1 e2 : DBExpr s .bool) : DBExpr s .bool
  | const : (asType t) → DBExpr s t
deriving Repr

def DBExpr.evaluate (row : Row s) : DBExpr s t → (asType t)
| .col _ loc => Row.get row loc
| .eq e1 e2 => evaluate row e1 == evaluate row e2
| .lt e1 e2  => evaluate row e1 < evaluate row e2
| .and e1 e2 => evaluate row e1 && evaluate row e2
| .const v => v

abbrev Query : Schema → Type := RA.Query DBType asType
export RA.Query (table union diff select project product renameColumn prefixWith)
abbrev Query.exec : {s : Schema} → Query s → Table s :=
  RA.Query.exec DBType asType

macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))

----------------------------------------
def tallInDenmark0 : DBExpr peak .bool :=
  .and (.lt (.const 1000) (.col "elevation" (by repeat constructor)))
       (.eq (.col "location" (by repeat constructor)) (.const "Denmark"))

def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (c! "elevation"))
       (.eq (c! "location") (.const "Denmark"))

#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, 2023)
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)

-- перевод DBExpr в фильтр для select
-- (для типов БД, которые переходят в Bool)
def flt (e : DBExpr s t) (eq : asType t = Bool) : (Row s → Bool) :=
  fun r => eq ▸ e.evaluate r

macro "⸨" e:term "⸩" : term => `(flt $e rfl)

-- open Query in
def example1  :=
  table mountainDiary |>.select ⸨.lt (.const 500) (c! "elevation")⸩
  |>.project [⟨"elevation", .int⟩] (by repeat constructor)

#eval example1.exec

-- это нужно для применения product ниже
theorem t1 : Tables.disjoint ["mountain.name", "mountain.location", "mountain.elevation", "mountain.lastVisited"]
  ["waterfall.name", "waterfall.location", "waterfall.lastVisited"] = true :=
  by exact rfl

-- open RA.Query in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfall := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfall t1
    |>.select ⸨.eq (c! "mountain.location") (c! "waterfall.location")⸩
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩] (by repeat constructor)

#eval example2.exec
