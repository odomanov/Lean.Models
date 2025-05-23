-- пример трансформации ER-модели в RA-модель

import ERModel.ERtoRA                -- файл задаёт правила обработки ER-модели
-- import Lib.Alldecls
open RA.Tables

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

-- Проверяем, что создались типы, таблицы и пр.

open ER1
#check DBType
#check DBType.address
#print DBType.asType       -- таблица типов
#check Schema
#check Table

#check DepartmentIdent
#check Department
#print Employee

open DepartmentIdent EmployeeIdent
#eval Department
#print EmployeeSchema
#eval Employee
#print Dept_EmplSchema     -- схема таблицы связи
#eval Dept_Empl            -- сама таблица


---=== Запросы в реляционной алгебре ===

open RA

-- функция проверки департамента в первой колонке
def DeptIs (d : DepartmentIdent) (r : Row DepartmentSchema) : Bool :=
  let v := Row.get r .here; v == d

-- Собственно запросы

def q1 := Query.select (Query.table Department) (DeptIs «ОК»)    -- отбор по департаменту
#reduce q1.exec
def q2 := Query.select (Query.table Department) (DeptIs «Трансп.цех»)
#reduce q2.exec
def q3 := Query.product (Query.table Department) (Query.prefixWith "C" (Query.table Dept_Empl)) (by constructor)
#reduce q3.exec

-- #alldecls
