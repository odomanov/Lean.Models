/- Формализация предметной области без оглядки на RA и ER.
   3 сущности: Department, Employee, Project
   4 связи: 1) работники отдела: Dept_Emp
            2) начальник-подчинённый: Empl_Dep
            3) руководитель-проект: Manager_Proj
            4) проект-участники: Proj_Worker

TODO: атрибуты отношений                               -/

import ERModel.RelationsDep
open DepRel

--== Значения (values) ==-----------

def First_name  := { s : String // s ≠ "" }
def Second_name := { s : String // s ≠ "" }
def Empl_no     := { n : Nat // n ≤ 2000 }
def Age         := { n : Nat // n ≥ 20 ∧ n ≤ 100 }
def Str         := { s : String // s ≠ "" }
def Proj_no     := { n : Nat // n ≤ 1000 }
def Percentage  := { x : Float // x ≥ 0 ∧ x ≤ 100 }  -- для Proj_Worker
deriving instance BEq, Repr for First_name
deriving instance BEq, Repr for Second_name
deriving instance BEq, Repr for Empl_no
deriving instance BEq, Repr for Age
deriving instance BEq, Repr for Str
deriving instance BEq, Repr for Proj_no
-- deriving instance BEq, Repr for Percentage

notation "‹" n "›" => ⟨n, by native_decide⟩


--== Сущности ==-----------------------------------
-- Задаются набором атрибутов.

structure DepartmentAttrs where
  name : Str
deriving BEq, Repr

structure EmployeeAttrs where
  emp_no : Empl_no
  name   : First_name × Second_name
  age    : Age
deriving BEq, Repr

structure ProjectAttrs where
  proj_no : Proj_no
deriving BEq, Repr

-- тип, собирающий все сущности
inductive EntityAttrs where
| dept (d : DepartmentAttrs)
| empl (e : EmployeeAttrs)
| proj (p : ProjectAttrs)

-- сущности

inductive Department : DepartmentAttrs → Type where
| «Трансп.цех» : Department ‹"Транспортный цех"›
| «ОК»         : Department ‹"Отдел кадров"›
deriving Repr
open Department

inductive Employee : EmployeeAttrs → Type where
| «Джон Доу»  : Employee ⟨ ‹1000›, (‹"John"›, ‹"Doe"›), ‹20› ⟩
| «Джон Доу'» : Employee ⟨ ‹1000›, (‹"John"›, ‹"Doe"›), ‹20› ⟩
| «Мэри Кью»  : Employee ⟨ ‹1001›, (‹"Mary"›, ‹"Kew"›), ‹25› ⟩
| «Мэри Энн»  : Employee ⟨ ‹1002›, (‹"Mary"›, ‹"Ann"›), ‹25› ⟩
deriving Repr
open Employee

inductive Project : ProjectAttrs → Type where
| Pr1 : Project ‹600›
| Pr2 : Project ‹700›
deriving Repr
open Project

-- функции чтения атрибутов
def Department.get_attrs : Department r → DepartmentAttrs := fun _ => r
def Employee.get_attrs : Employee r → EmployeeAttrs := fun _ => r
def Project.get_attrs : Project r → ProjectAttrs := fun _ => r

example : «ОК».get_attrs = { name := ‹"Отдел кадров"› } := rfl
#eval «Мэри Кью».get_attrs
example : «Мэри Кью».get_attrs = { emp_no := ‹1001›, name := (‹"Mary"›, ‹"Kew"›), age := ‹25› } := rfl


--== Связи ==------------------------------------

-- Связь "работники департамента" --

inductive Dept_Empl : Rel Department Employee where
| de1 : Dept_Empl ⟨«Трансп.цех», «Джон Доу»⟩
| de2 : Dept_Empl ⟨«Трансп.цех», «Мэри Кью»⟩
| de3 : Dept_Empl ⟨«ОК», «Мэри Энн»⟩
-- | de4 : Dept_Empl ⟨«ОК», «Мэри Кью»⟩  -- error
deriving Repr
open Dept_Empl

-- Dept_Empl вместе с условием 1:N
def Dept_Empl1N : Rel_1N Department Employee where
  val := Dept_Empl
  property := by proveIs1N

-- роли (относительно отношения)

def Dept_Empl.«место работы» {r : RELs (Department attd) (Employee atte)} (_ : Dept_Empl r)
  : Department attd := r.left
def Dept_Empl.«работник» {r : RELs (Department attd) (Employee atte)} (_ : Dept_Empl r)
  : Employee atte := r.right

-- примеры
example : Dept_Empl.«работник» de1 = «Джон Доу» := rfl
example : Dept_Empl.de1.«место работы» = «Трансп.цех» := rfl

-- рабочие места сотрудника e
def workplace (e : Employee atte) := Σ attd, Σ (d : Department attd), Dept_Empl ⟨d, e⟩
#check workplace «Джон Доу»
example : workplace «Джон Доу» := ⟨_,«Трансп.цех»,by constructor⟩

-- теорема: у каждого работника только одно место работы
theorem t1 : ∀ (e : Employee atte) (d1 : Department attd1) (d2 : Department attd2),
  Dept_Empl ⟨d1,e⟩ → Dept_Empl ⟨d2,e⟩ → HEq d1 d2 := by
  intro e d1 d2 x y
  cases x <;> cases y <;> trivial


-- Связь "Подчинённые-начальник" (dependents), N:1 ---------------------------------

inductive Empl_Dep : Rel Employee Employee where
| ed1 : Empl_Dep ⟨«Джон Доу», «Мэри Кью»⟩
| ed2 : Empl_Dep ⟨«Мэри Энн», «Мэри Кью»⟩
deriving Repr
open Empl_Dep

def Empl_DepN1 : Rel_N1 Employee Employee where
  val := Empl_Dep
  property := by proveIsN1

def Empl_Dep.«подчинённый» {r : RELs (Employee att1) (Employee att2)} (_ : Empl_Dep r)
  : Employee att1 := r.left
def Empl_Dep.«начальник» {r : RELs (Employee att1) (Employee att2)} (_ : Empl_Dep r)
  : Employee att2 := r.right

-- проект-исполнители ----------------------------------------------

inductive Proj_Worker : Rel Project Employee where
| pw1 : Proj_Worker ⟨Pr1, «Джон Доу»⟩
| pw2 : Proj_Worker ⟨Pr1, «Мэри Кью»⟩
| pw3 : Proj_Worker ⟨Pr2, «Мэри Энн»⟩

def Proj_Worker1N : Rel_1N Project Employee where
  val := Proj_Worker
  property := by proveIs1N

def Proj_Worker.«проект» {r : RELs (Project attp) (Employee atte)} (_ : Proj_Worker r)
  : Project attp := r.left
def Proj_Worker.«участник проекта» {r : RELs (Project attp) (Employee atte)} (_ : Proj_Worker r)
  : Employee atte := r.right

-- руководитель-проекты -------

inductive Manager_Proj : Rel Employee Project where
| mp1 : Manager_Proj ⟨«Мэри Кью», Pr1⟩
| mp2 : Manager_Proj ⟨«Джон Доу», Pr2⟩
-- | mp3 : Manager_Proj ⟨«Мэри Энн», Pr1⟩
-- | mp4 : Manager_Proj ⟨«Мэри Кью», Pr2⟩
open Manager_Proj

def Manager_Proj11 : Rel_11 Employee Project where
  val := Manager_Proj
  property := by proveIs11

def Manager_Proj.«рук.проекта» {r : RELs (Employee atte) (Project attp)} (_ : Manager_Proj r)
  : Employee atte := r.left
def Manager_Proj.«проект» {r : RELs (Employee atte) (Project attp)} (_ : Manager_Proj r)
  : Project attp := r.right

#reduce mp1.«рук.проекта»
example : mp1.«рук.проекта» = «Мэри Кью» := rfl
example : mp2.«проект» = Pr2 := rfl

--------------------------------
-- собираем отношения в один тип

inductive Relationship where
| de (R : Dept_Empl r)    : Relationship
| ed (R : Empl_Dep r)     : Relationship
| pw (R : Proj_Worker r)  : Relationship
| mp (R : Manager_Proj r) : Relationship

example : Relationship := .de .de1
example : Relationship := .pw .pw2

-- def Relationship.«место работы» : (r : Relationship) → Option (Department attd)
-- | de R => some R.«место работы»
-- | _ => none

-- #reduce (Relationship.de .de1).«место работы»
-- #reduce (Relationship.de .de3).«место работы»
-- #reduce (Relationship.pw .pw3).«место работы»
