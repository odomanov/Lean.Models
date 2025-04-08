-- ER Model DSL - test
import Lean
import ERModel.DSL

-- Задаём модель. Пока только атрибуты.
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
