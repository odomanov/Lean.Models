-- пример применения реляционной алгебры RA
import Relations.Tables
import Relations.Tables_test      -- здесь заданы DBType и asType и определены нктр таблицы
import Relations.RA

-- читаем определения из RA и Tables в наше namespace
abbrev Query : Schema → Type := RA.Query DBType asType
namespace Query
export RA.Query (table union diff select project product renameColumn prefixWith)
end Query
abbrev Query.exec : {s : Schema} → Query s → Table s :=
  RA.Query.exec DBType asType
abbrev Row.get : Row s → HasCol s n t→ (asType t) :=
  Tables.Row.get DBType asType

-- определяем выражения для работы с данными (действуют на строку, см.ниже)
inductive DBExpr (s : Schema) : DBType → Type where
  | col (n : String) (loc : Tables.HasCol DBType s n t) : DBExpr s t
  | eq (e1 e2 : DBExpr s t) : DBExpr s .bool
  | lt (e1 e2 : DBExpr s .int) : DBExpr s .bool
  | and (e1 e2 : DBExpr s .bool) : DBExpr s .bool
  | const : (asType t) → DBExpr s t
deriving Repr

-- функция вычисления выражения DBExpr для строки row
def DBExpr.evaluate (row : Row s) : DBExpr s t → (asType t)
| .col _ loc => Row.get row loc
| .eq e1 e2 => evaluate row e1 == evaluate row e2
| .lt e1 e2  => evaluate row e1 < evaluate row e2
| .and e1 e2 => evaluate row e1 && evaluate row e2
| .const v => v

-- синтаксис для удобства
macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))

----------------------------------------
-- примеры работы с таблицами из Rel1

-- выражение DBExpr
def tallInDenmark0 : DBExpr peak .bool :=
  .and (.lt (.const 1000) (.col "elevation" (by repeat constructor)))
       (.eq (.col "location" (by repeat constructor)) (.const "Denmark"))

-- то же, но с синтаксическим сахаром
def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (c! "elevation"))
       (.eq (c! "location") (.const "Denmark"))

-- проверяем работу evaluate
#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, 2023)
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)

-- перевод DBExpr в фильтр для select
-- (для типов БД, которые переходят в Bool; eq -- док-во этого)
def flt (e : DBExpr s t) (eq : asType t = Bool) : (Row s → Bool) :=
  fun r => eq ▸ e.evaluate r

-- обозначение для удобства
macro "⸨" e:term "⸩" : term => `(flt $e rfl)

-- запросы к БД

open Query in
def example1  :=
  table mountainDiary |>.select ⸨.lt (.const 500) (c! "elevation")⸩
  |>.project [⟨"elevation", .int⟩] (by repeat constructor)

#eval example1.exec

open Query in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfall := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfall (by exact rfl)
    |>.select ⸨.eq (c! "mountain.location") (c! "waterfall.location")⸩
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩] (by repeat constructor)

#eval example2.exec
