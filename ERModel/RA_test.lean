-- тест для реляционной алгебры
import ERModel.RA
-- import Lib.Alldecls
open RA Tables

inductive DepartmentIdent : Type where | «Трансп.цех» | «ОК»
deriving Repr, BEq
open DepartmentIdent
inductive EmployeeIdent where | «Джон Доу» | «Мэри Кью» | «Мэри Энн»
deriving Repr, BEq
open EmployeeIdent
inductive ProjectIdent where | Pr1 | Pr2
deriving Repr, BEq
open ProjectIdent

inductive DBType : Type where
| name
| id
| address
| emp_no
| age
| num
| str
| work_place
| DepartmentDBT
| EmployeeDBT
| ProjectDBT
deriving BEq, Repr
open DBType

def DBType.asType : DBType → Type
| name       => String × String
| id         => Nat
| address    => String
| emp_no     => { n : Nat // n ≥ 1000 }
| age        => { a : Nat // a ≥ 18 ∧ a < 100 }
| num        => Nat
| str        => { s : String // s ≠ "" }                            -- непустая строка
| work_place => { l : List String // l.length > 0 ∧ l.length < 4}   -- список длины 1..3
| DepartmentDBT => DepartmentIdent
| EmployeeDBT   => EmployeeIdent
| ProjectDBT    => ProjectIdent

instance : DBconfig where
  DBType := DBType
  asType := DBType.asType

abbrev DepartmentSchema : Schema := [
  ⟨"Department", DepartmentDBT ⟩,
  ⟨"name", str⟩
]
def Department : Table DepartmentSchema := [
  («Трансп.цех», ⟨"Транспортный цех", by simp⟩),
  ( «ОК», ⟨"Отдел кадров", by simp⟩)
]

abbrev EmployeeSchema : Schema := [
  ⟨"Employee", EmployeeDBT⟩,
  ⟨ "emp_no", emp_no⟩,
  ⟨ "name", name⟩,
  ⟨ "age", age⟩
]
def Employee : Table EmployeeSchema := [
  («Джон Доу», ⟨1000,by simp⟩, ("John", "Doe"), ⟨20,by simp⟩),
  («Мэри Кью», ⟨1001,by simp⟩, ("Mary", "Kew"), ⟨25,by simp⟩),
  («Мэри Энн», ⟨1002,by simp⟩, ("Mary", "Ann"), ⟨25,by simp⟩)
]
abbrev ProjectSchema : Schema := [ ⟨"proj_no", num⟩ ]
instance : OfNat (Row ProjectSchema) n where ofNat := n
def Project : Table ProjectSchema := [ 600, 700 ]


-- проверка операций реляционной алгебры (select)

instance : BEq (DBconfig.asType t) where
  beq := match t with
    | .name       => @BEq.beq (String × String) _
    | .id         => @BEq.beq Nat _
    | .address    => @BEq.beq String _
    | .emp_no     => @BEq.beq { n : Nat // n ≥ 1000 } _
    | .age        => @BEq.beq { a : Nat // a ≥ 18 ∧ a < 100 } _
    | .num        => @BEq.beq Nat _
    | .str        => @BEq.beq { s : String // s ≠ "" } _
    | .work_place => @BEq.beq { l : List String // l.length > 0 ∧ l.length < 4} _
    | .DepartmentDBT => @BEq.beq DepartmentIdent _
    | .EmployeeDBT   => @BEq.beq EmployeeIdent _
    | .ProjectDBT    => @BEq.beq ProjectIdent _

-- условие для выбора из таблицы (select)
def DeptIs (d : DepartmentIdent) (r : Row DepartmentSchema) : Bool :=
  let v := Row.get r .here;  v == d

-- выбор из таблицы (по значению в столбце DepartmentIdent)
def q1 := RA.Query.select (RA.Query.table Department) (DeptIs «ОК»)
#reduce q1.exec
def q2 := RA.Query.select (RA.Query.table Department) (DeptIs «Трансп.цех»)
#reduce q2.exec

-- #alldecls
