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
    (work_place => String)
    (emp_no     => Nat)
    (age        => Nat)
    (num        => Nat)
    (str        => String)
    (DepartmentDBT => DepartmentIdent)
    (EmployeeDBT   => EmployeeIdent)
  Tables
    DepartmentSchema
      ("Depatment" : DepartmentDBT)
      ("name" : str)
      Department
        {(«Трансп.цех», "Транспортный цех")}
        {(«ОК», "Отдел кадров")}
  Tables
    EmployeeSchema
      ("Employee" : EmployeeDBT)
      ("emp_no" : emp_no)
      ("name"   : name)
      ("age"    : age)
      Employee
        {(«Джон Доу», (1000 : Nat), ("John", "Doe"), (20 : Nat))}
        {(«Мэри Кью», (1001 : Nat), ("Mary", "Kew"), (25 : Nat))}
        {(«Мэри Энн», (1002 : Nat), ("Mary", "Ann"), (25 : Nat))}
  Tables
    ProjectSchema
      ("proj_no" : num)
      Project
        {((600 : Nat))}
        {((700 : Nat))}
endRAModel

instance : BEq (RA2.DBType.asType t) where
  beq := match t with
    | .name       => @BEq.beq (String × String) _
    | .id         => @BEq.beq Nat _
    | .address    => @BEq.beq String _
    | .work_place => @BEq.beq String _
    | .emp_no     => @BEq.beq Nat _
    | .age        => @BEq.beq Nat _
    | .num        => @BEq.beq Nat _
    | .str        => @BEq.beq String _
    | .DepartmentDBT => @BEq.beq DepartmentIdent _
    | .EmployeeDBT   => @BEq.beq EmployeeIdent _

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

def DeptIs (d : DepartmentIdent) (r : Row DepartmentSchema) : Bool :=
  let v := RA2.Row.get r .here;  v == d

def q1 := RA.Query.select (RA.Query.table Department) (DeptIs «ОК»)
#reduce q1.exec
def q2 := RA.Query.select (RA.Query.table Department) (DeptIs «Трансп.цех»)
#reduce q2.exec

-- #alldecls
