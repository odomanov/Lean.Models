-- тест для DSL реляционной алгебры
import ERModel.RA
-- import Lib.Alldecls
import ERModel.RA_DSL

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
  Tables
    SchemaDepartment
      ("name" : str)
      Department
        {("Транспортный цех")}
        {("Отдел кадров")}
  Tables
    SchemaEmployee
      ("emp_no" : emp_no)
      ("name"   : name)
      ("age"    : age)
      Employee
        {((1000 : Nat), ("John", "Doe"), (20 : Nat))}
        {((1001 : Nat), ("Mary", "Kew"), (25 : Nat))}
        {((1002 : Nat), ("Mary", "Ann"), (25 : Nat))}
  Tables
    SchemaProject
      ("proj_no" : num)
      Project
        {((600 : Nat))}
        {((700 : Nat))}
endRAModel


#check RA2.DBType
open RA2
#check DBType.asType
#check DBType.str.asType
#reduce DBType.str.asType

#check Tables.Schema
#check RA2.Schema
#check Schema
#check Table
#check Column
#check Department
#eval Department
#eval Employee
#eval Project


-- #alldecls
