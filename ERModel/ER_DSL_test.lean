-- DSL для ER-модели - пример
import Lean
import ERModel.ER_DSL           -- правила обработки ER-модели
-- import Lib.Alldecls
open Relations

-- Задаём модель

ERModel ER1 where
  Attributes                                  -- имена атрибутов и их соответствие типам Lean
    (name       => String × String)
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
        («ОК»         => ⟨ ⟨"Отдел кадров", by simp⟩ ⟩)
    Employee                          -- следующая сущность
      (emp_no : emp_no)               -- атрибуты сущности
      (name   : name)
      (age    : age)
      Items
        («Джон Доу»  => ⟨ ⟨1000,by simp⟩, ("John", "Doe"), ⟨20,by simp⟩ ⟩)
        («Джон Доу'» => ⟨ ⟨1000,by simp⟩, ("John", "Doe"), ⟨20,by simp⟩ ⟩)
        («Мэри Кью»  => ⟨ ⟨1001,by simp⟩, ("Mary", "Kew"), ⟨25,by simp⟩ ⟩)
        («Мэри Энн»  => ⟨ ⟨1002,by simp⟩, ("Mary", "Ann"), ⟨25,by simp⟩ ⟩)
    Project
      (proj_no : num)
      Items
        (Pr1 => ⟨ (600 : Nat) ⟩)
        (Pr2 => ⟨ (700 : Nat) ⟩)
        (Pr3 => ⟨ (800 : Nat) ⟩)
  Relationships
    Department («место работы») Employee («работник»)   -- работники отдела
    Dept_Empl "1N"
      («Трансп.цех» → «Джон Доу»)
      («Трансп.цех» → «Мэри Кью»)
      («ОК» → «Мэри Энн»)
    Employee («начальник») Employee («подчинённый»)      -- начальник-подчинённые
    Empl_Dep "1N"
      («Мэри Кью» → «Джон Доу»)
      («Мэри Кью» → «Мэри Энн»)
    Project («участвует в проекте») Employee («участник»)     -- участники проектов
    Proj_Worker "N1"
      (Pr1 → «Джон Доу»)
      (Pr2 → «Джон Доу»)
      (Pr3 → «Мэри Энн»)
    Employee («руководитель») Project («руководит проектом»)    -- руководители проектов
    Manager_Proj "11"
      («Мэри Кью» → Pr1)
      («Джон Доу» → Pr2)
      («Мэри Энн» → Pr3)
endERModel

-- Проверяем, что определились тип Attr и функция Attr.bind.

-- #print commandERModel_WhereAttributes_Endmodel
-- #check ER1.Attr
#check ER1.Attr.name

open ER1 Attr     -- <-----
#check name
example : address := "длод"
example : str := ⟨"длод", by simp⟩
example : name := ("длод", "уцзу")
example : work_place := ⟨["орор","длподла"],by simp⟩

-- Проверяем, что определились сущности

#check DepartmentAttrs.name
#check EmployeeAttrs.age
example : EmployeeAttrs := ⟨⟨1115,by simp⟩, ("лвоарпло", "лпрлар"), {val:=22, property:=by simp}⟩

-- Проверяем интерпретации сущностей

open Department
#check Department
#reduce Department.«Трансп.цех»
#reduce Employee.«Мэри Энн»


----------  Проверяем связи

open Department Employee Project

#check Dept_Empl
#print Dept_Empl
#check Dept_Empl «Трансп.цех» «Джон Доу»
example : Dept_Empl «Трансп.цех» «Джон Доу» := trivial
#check Dept_Empl1N
#check Dept_Empl1N.val
#reduce Dept_Empl1N.val
example : Dept_Empl1N.property = by proveIs1N := by simp

-- проверяем роли

def ex1 : Dept_EmplSRel := ⟨«Трансп.цех», «Джон Доу», .intro⟩
example : ex1.«работник» = «Джон Доу» := rfl
example : ex1.«место работы» = «Трансп.цех» := rfl


-- #alldecls
