import Lean
import ERModel.ER2RA
-- import Lib.Alldecls

ERModel ER1 where
  Attributes
    (name       => String × String)
    (id         => Nat)
    (address    => String)
    (work_place => String)
    (emp_no     => Nat)
    (age        => Nat)
    (num        => Nat)
    (str        => String)
  Entities
    Department
      (name : str)
      Items «Трансп.цех» «ОК»
      Binds
        («Трансп.цех» => ⟨ "Транспортный цех" ⟩)
        («ОК» => ⟨ "Отдел кадров" ⟩)
    Employee
      (emp_no : emp_no)
      (name   : name)
      (age    : age)
      Items «Джон Доу» «Мэри Кью» «Мэри Энн»
      Binds
        («Джон Доу» => ⟨ (1000 : Nat), ("John", "Doe"), (20 : Nat) ⟩)
        («Мэри Кью» => ⟨ (1001 : Nat), ("Mary", "Kew"), (25 : Nat) ⟩)
        («Мэри Энн» => ⟨ (1002 : Nat), ("Mary", "Ann"), (25 : Nat) ⟩)
    Project
      (proj_no : num)
      Items Pr1 Pr2
      Binds
        (Pr1 => ⟨ (600 : Nat) ⟩)
        (Pr2 => ⟨ (700 : Nat) ⟩)
endERModel

#check ER1.DBType
open ER1
#check DBType
#check DBType.address
#eval DBType.name

#check Tables.Schema
#check ER1.Schema
#check Schema
#check Table
#check Column
#check Department
#check Employee

-- #alldecls
