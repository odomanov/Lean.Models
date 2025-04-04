/- Entity–relationship model -- пример применения
   3 сущности: Department, Employee, Project
   4 связи: 1) работники департамента: Dept_Emp
            2) начальник-подчинённый: Emp_Dep
            3) руководитель-проект: Manager_Proj
            4) проект-участники: Proj_Worker              -/
import ERModel.ER
open ER

--== Атрибуты  ==-------------------

-- TODO: для атрибутов должна быть отдельная теория
inductive Attr where
| name | id | address | work_place | emp_no | age | num | str
deriving Repr
open Attr

-- какой-то произвольный набор атрибутов
def Attr.bind : Attr → Type
| .name => String × String
| .id => Nat
| .address => String
| .work_place => String
| .emp_no => Nat
| .age => Nat
| .num => Nat
| .str => String


--== Сущности (будут служить значениями идентификаторов) ==-----------------------------------
-- Задаются набором атрибутов.

structure Department where
  name : str.bind

structure Employee where
  emp_no : emp_no.bind
  name   : name.bind
  age    : age.bind

structure Project where
  proj_no : num.bind

-- тип, собирающий все сущности
inductive Entity where
| dep (d : Department)
| emp (e : Employee)
| prj (p : Project)

-- идентификаторы сущностей и их связи со значениями (binding)

inductive DepartmentIdent : Type where | «Трансп.цех» | «ОК»
open DepartmentIdent
def DepartmentIdent.bind : DepartmentIdent → Department
| «Трансп.цех» => ⟨ "Транспортный цех" ⟩
| «ОК» => ⟨ "Отдел кадров" ⟩

inductive EmployeeIdent where | «Джон Доу» | «Мэри Кью» | «Мэри Энн»
open EmployeeIdent
def EmployeeIdent.bind : EmployeeIdent → Employee
| «Джон Доу» => ⟨ (1000 : Nat), ("John", "Doe"), (20 : Nat) ⟩
| «Мэри Кью» => ⟨ (1001 : Nat), ("Mary", "Kew"), (25 : Nat) ⟩
| «Мэри Энн» => ⟨ (1002 : Nat), ("Mary", "Ann"), (25 : Nat) ⟩

inductive ProjectIdent where | Pr1 | Pr2 deriving Repr
def ProjectIdent.bind : ProjectIdent → Project
| .Pr1 => ⟨ (600 : Nat) ⟩
| .Pr2 => ⟨ (700 : Nat) ⟩

-- тип, собирающий все идентификаторы сущностей
inductive EntityIdent where
| dep (d : DepartmentIdent)
| emp (e : EmployeeIdent)
| prj (p : ProjectIdent)
def EntityIdent.bind : EntityIdent → Entity
| dep d => .dep d.bind
| emp e => .emp e.bind
| prj p => .prj p.bind

-- сущности, являющиеся значениями (т.е. имеющие идентификаторы)
abbrev DepartmentE := mkE DepartmentIdent.bind
abbrev EmployeeE   := mkE EmployeeIdent.bind
abbrev ProjectE    := mkE ProjectIdent.bind

--== Связи ==------------------------------------

-- Связь "работники департамента" --

-- исходное отношение (на идентификаторах)
def Dept_EmpIdentBase : REL DepartmentIdent EmployeeIdent
  | «Трансп.цех», «Джон Доу» => True
  | «Трансп.цех», «Мэри Кью» => True
  | «ОК», «Мэри Энн» => True
  | _, _ => False

-- теорема: Dept_EmpIdentBase удовлетворяет условию Is1N
theorem c1 : Is1N Dept_EmpIdentBase
  | «Джон Доу», «Трансп.цех», «Трансп.цех», .intro, .intro => by simp
  | «Мэри Кью», «Трансп.цех», «Трансп.цех», .intro, .intro => rfl
  | «Мэри Энн», «ОК», «ОК», .intro, .intro => rfl

-- Dept_EmpIdentBase вместе с условием 1:N
def Dept_EmpIdent1N : REL_1N DepartmentIdent EmployeeIdent where
  pred := Dept_EmpIdentBase
  cond := c1

def Dept_EmpIdent1N.bind := REL_1N.bind DepartmentIdent.bind EmployeeIdent.bind

-- TODO: добавляем атрибуты к отношению в целом
-- .pred, .cond, ...
-- structure Dept_EmpIdentEXT extends REL_1N DepartmentIdent EmployeeIdent where
--   attr1 : str.bind

---------------

-- Rel для идентификаторов и значений
abbrev Dept_EmpIdentRel := Rel_1N Dept_EmpIdent1N
abbrev Dept_EmpRel := Rel_1N (REL_1N.bind DepartmentIdent.bind EmployeeIdent.bind Dept_EmpIdent1N)
def Dept_EmpRel.bind := Rel.bind DepartmentIdent.bind EmployeeIdent.bind Dept_EmpIdent1N.pred

-- роли (для идентификаторов)
def Dept_EmpIdentRel.«место работы» (r : Dept_EmpIdentRel) : DepartmentIdent := r.src
def Dept_EmpIdentRel.«работник»     (r : Dept_EmpIdentRel) : EmployeeIdent   := r.tgt

-- роли (для значений)
def Dept_EmpRel.«место работы» (r : Dept_EmpRel) : DepartmentE := r.src
def Dept_EmpRel.«работник»     (r : Dept_EmpRel) : EmployeeE   := r.tgt

-- примеры
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
example : der.«работник».1 = { emp_no := (1000 : Nat), name := ("John", "Doe"), age := (20 : Nat) } := rfl
example : der.«работник».1 = ⟨(1000 : Nat), ("John", "Doe"), (20 : Nat)⟩ := rfl
example : der.«место работы».1 = { name := "Транспортный цех" } := rfl
example : der.«место работы».1 = ⟨"Транспортный цех"⟩ := rfl

-- Начальник-подчинённый (employee-dependents) -----------------------------------------

abbrev Emp_DepIdentBase := REL EmployeeIdent EmployeeIdent
def Emp_DepIdent : Emp_DepIdentBase
  | «Джон Доу», «Мэри Кью» => True
  | «Мэри Энн», «Мэри Кью» => True
  | _, _ => False

theorem c2 : IsN1 Emp_DepIdent
  | «Джон Доу», «Мэри Кью», «Мэри Кью», .intro, .intro => by simp
  | «Мэри Энн», «Мэри Кью», «Мэри Кью», .intro, .intro => by simp

def Emp_DepIdentN1 : REL_N1 EmployeeIdent EmployeeIdent where
  pred := Emp_DepIdent
  cond := c2

def Emp_DepIdentN1.bind := REL_N1.bind EmployeeIdent.bind EmployeeIdent.bind

abbrev Emp_DepIdentRel := Rel_N1 Emp_DepIdentN1
abbrev Emp_DepRel := Rel_N1 (REL_N1.bind EmployeeIdent.bind EmployeeIdent.bind Emp_DepIdentN1)
def Emp_DepRel.bind := Rel.bind EmployeeIdent.bind EmployeeIdent.bind Emp_DepIdentN1.pred

def Emp_DepRel.«начальник» (r : Emp_DepRel) : EmployeeE := r.src
def Emp_DepRel.«подчинённый» (r : Emp_DepRel) : EmployeeE := r.tgt

-- проект-исполнители ----------------------------------------------

def Proj_WorkerIdentBase : REL ProjectIdent EmployeeIdent
| .Pr1, «Джон Доу» => True
| .Pr1, «Мэри Кью» => True
| .Pr2, «Мэри Энн» => True
| _, _ => False

theorem c3 : Is1N Proj_WorkerIdentBase
  | «Джон Доу», .Pr1, .Pr1, .intro, .intro => by simp!
  | «Мэри Энн», .Pr2, .Pr2, .intro, .intro => by simp!
  | «Мэри Кью», .Pr1, .Pr1, .intro, .intro => by simp!

def Proj_WorkerIdent1N : REL_1N ProjectIdent EmployeeIdent where
  pred := Proj_WorkerIdentBase
  cond := c3

def Proj_WorkerIdent1N.bind := REL_1N.bind ProjectIdent.bind EmployeeIdent.bind

-- TODO: добавление атрибута к связи в целом
-- structure Proj_Worker extends Rel_1N Proj_WorkerIdent1N where
--   attr1 : str.bind

-----------

abbrev Proj_WorkerIdentRel := Rel_1N Proj_WorkerIdent1N
abbrev Proj_WorkerRel := Rel_1N (REL_1N.bind ProjectIdent.bind EmployeeIdent.bind Proj_WorkerIdent1N)
def Proj_WorkerRel.bind := Rel_1N.bind ProjectIdent.bind EmployeeIdent.bind Proj_WorkerIdent1N

def Proj_WorkerRel.«проект» (r : Proj_WorkerRel) : ProjectE := r.src
def Proj_WorkerRel.«участник проекта» (r : Proj_WorkerRel) : EmployeeE := r.tgt

-- руководитель-проекты -------

def Manager_ProjIdentBase : REL EmployeeIdent ProjectIdent
| «Мэри Кью», .Pr1 => True
| «Джон Доу», .Pr2 => True
| _, _ => False

theorem c4 : Is1N Manager_ProjIdentBase
| .Pr1, «Мэри Кью», «Мэри Кью», .intro, .intro => by simp!
| .Pr2, «Джон Доу», «Джон Доу», .intro, .intro => by simp!

def Manager_ProjIdent1N : REL_1N EmployeeIdent ProjectIdent where
  pred := Manager_ProjIdentBase
  cond := c4

def Manager_ProjIdent1N.bind := REL_1N.bind EmployeeIdent.bind ProjectIdent.bind

------------
abbrev Manager_ProjIdentRel := Rel_1N Manager_ProjIdent1N
abbrev Manager_ProjRel := Rel_1N (REL_1N.bind EmployeeIdent.bind ProjectIdent.bind Manager_ProjIdent1N)
def Manager_ProjRel.bind := Rel.bind EmployeeIdent.bind ProjectIdent.bind Manager_ProjIdent1N.pred

def Manager_ProjRel.«рук.проекта» (r : Manager_ProjRel) : EmployeeE := r.src
def Manager_ProjRel.«проект» (r : Manager_ProjRel) : ProjectE := r.tgt

--------------------------------
-- собираем отношения в один тип

inductive RelIdent where
| de (r : Dept_EmpIdentRel)
| ed (r : Emp_DepIdentRel)
| pw (r : Proj_WorkerIdentRel)
| mp (r : Manager_ProjIdentRel)
inductive Rel where
| de (r : Dept_EmpRel)
| ed (r : Emp_DepRel)
| pw (r : Proj_WorkerRel)
| mp (r : Manager_ProjRel)
def RelIdent.bind : RelIdent → Rel
| .de r => Rel.de (Dept_EmpRel.bind r)
| .ed r => Rel.ed (Emp_DepRel.bind r)
| .pw r => Rel.pw (Proj_WorkerRel.bind r)
| .mp r => Rel.mp (Manager_ProjRel.bind r)
