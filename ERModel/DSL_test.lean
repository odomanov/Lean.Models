-- ER Model DSL - test
import Lean
import ERModel.DSL

-- Задаём модель. Пока только атрибуты и сущности.
ERModel ER1 where
  Attributes
    (name => String × String)
    (id => Nat)
    (address => String)
    (work_place => String)
    (emp_no => Nat)
    (age => Nat)
    (num => Nat)
    (str => String)
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
endModel

-- Проверяем, что определились тип Attr и функция Attr.bind.

-- #print commandERModel_WhereAttributes_Endmodel
#check ER1.Attr
#check ER1.Attr.name
open ER1 Attr                 -- <-----
#check name
#check Attr.bind
#check Attr.bind Attr.name
example : Attr.address.bind := "длод"
example : str.bind := "длод"
example : name.bind := ("длод", "уцзу")
example : Attr.id.bind := (5 : Nat)

-- Проверяем, что определились сущности

#check Department.name
#check Employee.age
example : Employee := ⟨(1115 : Nat), ("лвоарпло", "лпрлар"), (22 : Nat)⟩

-- Проверяем интерпретации сущностей

open Department
#check DepartmentIdent.bind
#reduce DepartmentIdent.«Трансп.цех».bind
#reduce EmployeeIdent.«Мэри Энн».bind
