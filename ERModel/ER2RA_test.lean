-- пример трансформации ER-модели в RA-модель

import ERModel.ER2RA                -- файл задаёт правила обработки ER-модели
-- import Lib.Alldecls

ERModel ER1 where
  Attributes                                  -- имена атрибутов и их соответствие типам Lean
    (name       => String × String)
    (id         => Nat)
    (address    => String)
    (work_place => String)
    (emp_no     => Nat)
    (age        => Nat)
    (num        => Nat)
    (str        => String)
  Entities
    Department                        -- имя сущности
      (name : str)                    -- атрибуты сущности (в данном случае один)
      Items «Трансп.цех» «ОК»         -- идентификаторы
      Binds                           -- связь идентификаторов со значениями в Lean
        («Трансп.цех» => ⟨ "Транспортный цех" ⟩)
        («ОК» => ⟨ "Отдел кадров" ⟩)
    Employee                          -- следующая сущность
      (emp_no : emp_no)               -- атрибуты сущности
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
    | .work_place => @BEq.beq String _
    | .emp_no     => @BEq.beq Nat _
    | .age        => @BEq.beq Nat _
    | .num        => @BEq.beq Nat _
    | .str        => @BEq.beq String _
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
