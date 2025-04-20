-- пример трансформации ER-модели в RA-модель

import ERModel.ER2RA                -- файл задаёт правила обработки ER-модели
-- import Lib.Alldecls

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
      Items «Трансп.цех» «ОК»         -- идентификаторы
      Binds                           -- связь идентификаторов со значениями в Lean
        («Трансп.цех» => ⟨ ⟨ "Транспортный цех", by simp⟩ ⟩)
        («ОК» => ⟨ ⟨ "Отдел кадров", by simp⟩ ⟩)
    Employee                          -- следующая сущность
      (emp_no : emp_no)               -- атрибуты сущности
      (name   : name)
      (age    : age)
      Items «Джон Доу» «Мэри Кью» «Мэри Энн»
      Binds
        («Джон Доу» => ⟨ ⟨1000,by simp⟩, ("John", "Doe"), ⟨20,by simp⟩ ⟩)
        («Мэри Кью» => ⟨ ⟨1001,by simp⟩, ("Mary", "Kew"), ⟨25,by simp⟩ ⟩)
        («Мэри Энн» => ⟨ ⟨1002,by simp⟩, ("Mary", "Ann"), ⟨25,by simp⟩ ⟩)
    Project
      (proj_no : num)
      Items Pr1 Pr2
      Binds
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
#print Dept_EmpSchema     -- схема таблица связи
#eval Dept_Emp            -- сама таблица


---=== Запросы в реляционной алгебре ===

open RA

-- сначала некоторая подготовка (TODO: сделать автоматически)
instance : BEq (DBType.asType t) where
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

-- функция проверки департамента в первой колонке
def DeptIs (d : DepartmentIdent) (r : Row DepartmentSchema) : Bool :=
  let v := ER1.Row.get r .here; v == d

-- Собственно запросы

def q1 := Query.select (Query.table Department) (DeptIs «ОК»)    -- отбор по департаменту
#reduce q1.exec
def q2 := Query.select (Query.table Department) (DeptIs «Трансп.цех»)
#reduce q2.exec
def q3 := Query.product (Query.table Department) (Query.prefixWith "C" (Query.table Dept_Emp)) (by constructor)
#reduce q3.exec

-- #alldecls
