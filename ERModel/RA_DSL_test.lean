-- тест для DSL реляционной алгебры
import ERModel.RA
-- import Lib.Alldecls
import ERModel.RA_DSL
open RA.Tables RA_DSL

inductive DepartmentIdent : Type where | «Трансп.цех» | «ОК»
deriving Repr, BEq
open DepartmentIdent
inductive EmployeeIdent where | «Джон Доу» | «Мэри Кью» | «Мэри Энн»
deriving Repr, BEq
open EmployeeIdent
inductive ProjectIdent where | Pr1 | Pr2
deriving Repr, BEq
open ProjectIdent

RAModel RA2 where
  DBTypes
    (name       => String × String)
    (id         => Nat)
    (address    => String)
    (emp_no     => { n : Nat // n ≥ 1000 })
    (age        => { a : Nat // a ≥ 18 ∧ a < 100 })
    (num        => Nat)
    (str        => { s : String // s ≠ "" })                            -- непустая строка
    (work_place => { l : List String // l.length > 0 ∧ l.length < 4})   -- список длины 1..3
    (DepartmentDBT => DepartmentIdent)
    (EmployeeDBT   => EmployeeIdent)
    (ProjectDBT    => ProjectIdent)
  Tables
    DepartmentSchema
      ("Depatment" : DepartmentDBT)
      ("name" : str)
      Department
        {(«Трансп.цех», ⟨"Транспортный цех", by simp⟩)}
        {(«ОК», ⟨"Отдел кадров", by simp⟩)}
  Tables
    EmployeeSchema
      ("Employee" : EmployeeDBT)
      ("emp_no" : emp_no)
      ("name"   : name)
      ("age"    : age)
      Employee
        {(«Джон Доу», ⟨1000,by simp⟩, ("John", "Doe"), ⟨20,by simp⟩)}
        {(«Мэри Кью», ⟨1001,by simp⟩, ("Mary", "Kew"), ⟨25,by simp⟩)}
        {(«Мэри Энн», ⟨1002,by simp⟩, ("Mary", "Ann"), ⟨25,by simp⟩)}
  Tables
    ProjectSchema
      ("proj_no" : num)
      Project
        {((600 : Nat))}
        {((700 : Nat))}
endRAModel


-- Проверка того, что нужные типы и функции определились

open RA2
#check DBType.asType
#check DBType.str.asType
#reduce DBType.str.asType

#check Schema
#check RA2.Schema
#check Schema
#check Table
#check Column
#check Department
#reduce Department
#eval Department
#reduce Employee
#eval Project
#eval EmployeeSchema

-- open RA
#check RA.Query.table
#reduce RA.Query.table Employee
#check RA.Tables.Row.get
#check RA2.Row --DepartmentSchema
#check RA2.Row.get
#check Row
#check RA2.Schema.renameColumn
#reduce RA2.HasCol DepartmentSchema "Department" DBType.DepartmentDBT

-- проверка операций реляционной алгебры

instance : BEq (RA2.DBType.asType t) where
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
  let v := RA2.Row.get r .here;  v == d

-- выбор из таблицы (по значению в столбце DepartmentIdent)
def q1 := RA.Query.select (RA.Query.table Department) (DeptIs «ОК»)
#reduce q1.exec
def q2 := RA.Query.select (RA.Query.table Department) (DeptIs «Трансп.цех»)
#reduce q2.exec

-- #alldecls
