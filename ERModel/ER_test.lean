/- Entity–relationship model -- пример применения
   3 сущности: Department, Employee, Project
   4 связи: 1) работники отдела: Dept_Empl
            2) начальник-подчинённый: Empl_Dep
            3) руководитель-проект: Manager_Proj
            4) проект-участники: Proj_Worker              -/
import ERModel.Relations
open Relations

--== Атрибуты  ==-------------------

-- TODO: для атрибутов должна быть отдельная теория
-- какой-то произвольный набор атрибутов
def Attr.name       := String × String
def Attr.address    := String
def Attr.emp_no     := { n : Nat // n ≥ 1000 }
def Attr.age        := { a : Nat // a ≥ 18 ∧ a < 100 }
def Attr.num        := Nat
def Attr.str        := { s : String // s ≠ "" }                            -- непустая строка
def Attr.work_place := { l : List String // l.length > 0 ∧ l.length < 4}   -- список длины 1..3
open Attr

notation "‹" n "›" => ⟨n, by native_decide⟩

--== Сущности (будут служить значениями идентификаторов) ==-----------------------------------
-- Задаются набором атрибутов.

structure DepartmentAttrs where
  name : str

structure EmployeeAttrs where
  (emp_no : emp_no)
  (name   : name)
  (age    : age)

structure ProjectAttrs where
  proj_no : num

-- тип, собирающий все сущности
inductive EntityAttrs where
| dep (d : DepartmentAttrs)
| emp (e : EmployeeAttrs)
| prj (p : ProjectAttrs)

-- сущности и их атрибуты

inductive Department : Type where | «Трансп.цех» | «ОК»
open Department
def Department.attrs : Department → DepartmentAttrs
| «Трансп.цех» => ‹"Транспортный цех"›
| «ОК» => ‹"Отдел кадров"›
instance : Coe Department DepartmentAttrs where
  coe := Department.attrs

inductive Employee where | «Джон Доу» | «Джон Доу'» | «Мэри Кью» | «Мэри Энн»
open Employee
def Employee.attrs : Employee → EmployeeAttrs
| «Джон Доу»  => ⟨ ‹1000›, ("John", "Doe"), ‹20› ⟩
| «Джон Доу'» => ⟨ ‹1000›, ("John", "Doe"), ‹20› ⟩
| «Мэри Кью»  => ⟨ ‹1001›, ("Mary", "Kew"), ‹25› ⟩
| «Мэри Энн»  => ⟨ ‹1002›, ("Mary", "Ann"), ‹25› ⟩
instance : Coe Employee EmployeeAttrs where
  coe := Employee.attrs

-- проверка коэрсии
def f : EmployeeAttrs → EmployeeAttrs := fun x => x
theorem t1 : f «Джон Доу» = «Джон Доу'» := rfl

inductive Project where | Pr1 | Pr2 | Pr3 deriving Repr
def Project.attrs : Project → ProjectAttrs
| .Pr1 => ⟨ (600 : Nat) ⟩
| .Pr2 => ⟨ (700 : Nat) ⟩
| .Pr3 => ⟨ (800 : Nat) ⟩
instance : Coe Project ProjectAttrs where
  coe := Project.attrs

-- тип, собирающий все идентификаторы сущностей
inductive Entity where
| dep (d : Department)
| emp (e : Employee)
| prj (p : Project)
def Entity.attrs : Entity → EntityAttrs
| dep d => .dep d.attrs
| emp e => .emp e.attrs
| prj p => .prj p.attrs


--== Связи ==------------------------------------

-- Связь "работники департамента" --

-- исходное отношение (на идентификаторах)
def Dept_Empl : Rel Department Employee
  | «Трансп.цех», «Джон Доу» => True
  | «Трансп.цех», «Мэри Кью» => True
  | «ОК», «Мэри Энн» => True
  | _, _ => False

-- Dept_Empl вместе с условием 1:N
def Dept_Empl1N : Rel_1N Department Employee where
  val := Dept_Empl
  property := by proveIs1N

-- TODO: добавляем атрибуты к отношению в целом
-- .pred, .cond, ...
-- structure Dept_EmpIdentEXT extends REL_1N Department Employee where
--   attr1 : str.bind

---------------

-- SRel
abbrev Dept_EmplSRel := SRel_1N Dept_Empl1N

-- роли
def Dept_EmplSRel.«место работы» (r : Dept_EmplSRel) : Department := r.src
def Dept_EmplSRel.«работник»     (r : Dept_EmplSRel) : Employee   := r.tgt

-- примеры
def ex1 : Dept_EmplSRel := ⟨«Трансп.цех», «Джон Доу», .intro⟩
example : ex1.«работник» = «Джон Доу» := rfl
example : ex1.«место работы» = «Трансп.цех» := rfl


-- Связь "Начальник-подчинённый" (employee-dependents) -----------------------------------

def Empl_Dep : Rel Employee Employee
  | «Мэри Кью», «Джон Доу» => True
  | «Мэри Кью», «Мэри Энн» => True
  | _, _ => False

def Empl_Dep1N : Rel_1N Employee Employee where
  val := Empl_Dep
  property := by proveIs1N

abbrev Empl_DepSRel := SRel_1N Empl_Dep1N

def Empl_DepSRel.«начальник» (r : Empl_DepSRel) : Employee := r.src
def Empl_DepSRel.«подчинённый» (r : Empl_DepSRel) : Employee := r.tgt


-- Связь "проект-исполнители" N:1----------------------------------------------

def Proj_Worker : Rel Project Employee
| .Pr1, «Джон Доу» => True
| .Pr2, «Джон Доу» => True
-- | .Pr2, «Мэри Кью» => True
| .Pr3, «Мэри Энн» => True
| _, _ => False

def Proj_WorkerN1 : Rel_N1 Project Employee where
  val := Proj_Worker
  property := by proveIsN1

-- TODO: добавление атрибута к связи в целом
-- structure Proj_Worker extends Rel_1N Proj_WorkerIdent1N where
--   attr1 : str.bind

-----------

abbrev Proj_WorkerSRel := SRel_N1 Proj_WorkerN1

def Proj_WorkerSRel.«проект» (r : Proj_WorkerSRel) : Project := r.src
def Proj_WorkerSRel.«участник проекта» (r : Proj_WorkerSRel) : Employee := r.tgt


-- Связь "руководитель-проекты" -------

def Manager_Proj : Rel Employee Project
| «Мэри Кью», .Pr1 => True
| «Джон Доу», .Pr2 => True
| «Мэри Энн», .Pr3 => True
| _, _ => False

def Manager_Proj11 : Rel_11 Employee Project where
  val := Manager_Proj
  property := by proveIs11

abbrev Manager_ProjSRel := SRel_11 Manager_Proj11

def Manager_ProjSRel.«рук.проекта» (r : Manager_ProjSRel) : Employee := r.src
def Manager_ProjSRel.«проект» (r : Manager_ProjSRel) : Project := r.tgt
