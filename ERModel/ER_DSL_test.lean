-- DSL для ER-модели - пример
import Lean
import ERModel.ER_DSL           -- правила обработки ER-модели
-- import Lib.Alldecls
open ER

-- Задаём модель

ERModel ER1 where
  Attributes                                  -- имена атрибутов и их соответствие типам Lean
    (name       => String × String)
    (id         => Nat)
    (address    => String)
    (emp_no     => { n : Nat // n ≥ 1000 })
    (age        => { a : Nat // a ≥ 18 ∧ a < 100 })
    (num        => Nat)
    (str        => { s : String // s ≠ "" })                            -- непустая строка
    (work_place => { l : List String // l.length > 0 ∧ l.length < 4})   -- список длины 1..3
  Entities
    Department                        -- имя сущности
      (name : str)                    -- атрибуты сущности (в данном случае один)
      Items                           -- идентификаторы и атрибуты
        («Трансп.цех» => ⟨ ⟨"Транспортный цех", by simp⟩ ⟩)
        («ОК» => ⟨ ⟨"Отдел кадров", by simp⟩ ⟩)
    Employee                          -- следующая сущность
      (emp_no : emp_no)               -- атрибуты сущности
      (name   : name)
      (age    : age)
      Items
        («Джон Доу» => ⟨ ⟨1000,by simp⟩, ("John", "Doe"), ⟨20,by simp⟩ ⟩)
        («Мэри Кью» => ⟨ ⟨1001,by simp⟩, ("Mary", "Kew"), ⟨25,by simp⟩ ⟩)
        («Мэри Энн» => ⟨ ⟨1002,by simp⟩, ("Mary", "Ann"), ⟨25,by simp⟩ ⟩)
    Project
      (proj_no : num)
      Items
        (Pr1 => ⟨ (600 : Nat) ⟩)
        (Pr2 => ⟨ (700 : Nat) ⟩)
  Relationships
    Department («место работы») Employee («работник»)   -- работники отдела
    Dept_Emp "1N"
      («Трансп.цех» → «Джон Доу»)
      («Трансп.цех» → «Мэри Кью»)
      («ОК» → «Мэри Энн»)
    Employee («начальник») Employee («подчинённый»)      -- начальник-подчинённые
    Emp_Dep "1N"
      («Мэри Кью» → «Джон Доу»)
      («Мэри Кью» → «Мэри Энн»)
    Project («участвует в проекте») Employee («участник»)     -- участники проектов
    Proj_Worker "1N"
      (Pr1 → «Мэри Кью»)
      (Pr1 → «Джон Доу»)
      (Pr2 → «Мэри Энн»)
    Employee («руководитель») Project («руководит проектом»)    -- руководители проектов
    Manager_Proj "11"
      («Мэри Кью» → Pr1)
      («Джон Доу» → Pr2)
endERModel

-- Проверяем, что определились тип Attr и функция Attr.bind.

-- #print commandERModel_WhereAttributes_Endmodel
#check ER1.Attr
#check ER1.Attr.name

open ER1 Attr     -- <-----
#check name
#check Attr.bind
#check Attr.bind Attr.name
example : Attr.address.bind := "длод"
example : str.bind := ⟨"длод", by simp⟩
example : name.bind := ("длод", "уцзу")
example : Attr.id.bind := (5 : Nat)
example : work_place.bind := ⟨["орор","длподла"],by simp⟩

-- Проверяем, что определились сущности

#check Department.name
#check Employee.age
example : Employee := ⟨⟨1115,by simp⟩, ("лвоарпло", "лпрлар"), {val:=22, property:=by simp}⟩

-- Проверяем интерпретации сущностей

open Department
#check DepartmentIdent.bind
#reduce DepartmentIdent.«Трансп.цех».bind
#reduce EmployeeIdent.«Мэри Энн».bind

#check DepartmentE
#check ProjectE

----------  Проверяем связи

open DepartmentIdent EmployeeIdent ProjectIdent

#check Dept_EmpIdentBase
#print Dept_EmpIdentBase
#check Dept_EmpIdentBase «Трансп.цех» «Джон Доу»
example : Dept_EmpIdentBase «Трансп.цех» «Джон Доу» := trivial
#check Dept_EmpIdent1N
#check Dept_EmpIdent1N.val
#reduce Dept_EmpIdent1N.val
example : Dept_EmpIdent1N.property = by proveIs1N := by simp

-- проверяем роли

def ex1 : Dept_EmpIdentRel := ⟨«Трансп.цех», «Джон Доу», .intro⟩
example : ex1.«работник» = «Джон Доу» := rfl
example : ex1.«место работы» = «Трансп.цех» := rfl

def d1 := XᵢtoX DepartmentIdent.bind DepartmentIdent.«Трансп.цех»
#reduce d1
def e1 := XᵢtoX EmployeeIdent.bind EmployeeIdent.«Джон Доу»
#reduce e1
def der : Dept_EmpRel := ⟨d1, e1, .intro⟩
#reduce der

#reduce der.«работник».1
#reduce der.«место работы».1
example : der.«работник».1 =
  { emp_no := ⟨1000,by simp⟩, name := ("John", "Doe"), age := ⟨20,by simp⟩ } := rfl
example : der.«работник».1 = ⟨⟨1000,by simp⟩, ("John", "Doe"), ⟨20,by simp⟩⟩ := rfl
example : der.«место работы».1 = { name := ⟨"Транспортный цех",by simp⟩ } := rfl
example : der.«место работы».1 = ⟨"Транспортный цех",by simp⟩ := rfl


-- #alldecls
