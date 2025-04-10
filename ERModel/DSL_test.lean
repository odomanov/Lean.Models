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
      (name : str.bind)
    Employee
      (emp_no : emp_no.bind)
      (name   : name.bind)
      (age    : age.bind)
    Project
      (proj_no : Attr.num.bind)
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
