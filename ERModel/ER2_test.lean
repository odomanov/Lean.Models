/- Entity–relationship model -- пример применения
   3 сущности: Department, Employee, Project
   4 связи: 1) работники отдела: Dept_Emp
            2) начальник-подчинённый: Empl_Dep
            3) руководитель-проект: Manager_Proj
            4) проект-участники: Proj_Worker              -/
import ERModel.ER2
open ER

--== Атрибуты  ==-------------------

-- TODO: для атрибутов должна быть отдельная теория
inductive Attr where
| name | id | address | work_place | emp_no | age | num | str
deriving Repr
open Attr

-- какой-то произвольный набор атрибутов
def Attr.bind : Attr → Type
| .name       => String × String
| .id         => Nat
| .address    => String
| .emp_no     => { n : Nat // n ≥ 1000 }
| .age        => { a : Nat // a ≥ 18 ∧ a < 100 }
| .num        => Nat
| .str        => { s : String // s ≠ "" }                            -- непустая строка
| .work_place => { l : List String // l.length > 0 ∧ l.length < 4}   -- список длины 1..3


--== Сущности ==-----------------------------------

-- наборы атрибутов, которые могут приписываться сущностям

structure DepartmentAttrs where
  name : str.bind

structure EmployeeAttrs where
  (emp_no : emp_no.bind)
  (name   : name.bind)
  (age    : age.bind)

structure ProjectAttrs where
  proj_no : num.bind

-- тип, собирающий все атрибуты сущностей
inductive EntityAttrs where
| dept (d : DepartmentAttrs)
| empl (e : EmployeeAttrs)
| proj (p : ProjectAttrs)


-- сущности и их атрибуты.
-- Задаются как функции из типов сущности в набор их атрибутов. Это означает,
-- что мы допускаем, что несколько сущностей могут иметь одинаковые атрибуты
-- (см., для примера, «Джон Доу» и «Джон Доу'»).

inductive Department : Type where | «Трансп.цех» | «ОК»
open Department

def Department.bind : Department → DepartmentAttrs
| «Трансп.цех» => ⟨ "Транспортный цех", by simp ⟩
| «ОК»         => ⟨ "Отдел кадров", by simp ⟩

inductive Employee where | «Джон Доу» | «Джон Доу'» | «Мэри Кью» | «Мэри Энн»
open Employee

def Employee.bind : Employee → EmployeeAttrs
| «Джон Доу»  => ⟨ ⟨1000,by simp⟩, ("John", "Doe"), ⟨20,by simp⟩ ⟩
| «Джон Доу'» => ⟨ ⟨1000,by simp⟩, ("John", "Doe"), ⟨20,by simp⟩ ⟩
| «Мэри Кью»  => ⟨ ⟨1001,by simp⟩, ("Mary", "Kew"), ⟨25,by simp⟩ ⟩
| «Мэри Энн»  => ⟨ ⟨1002,by simp⟩, ("Mary", "Ann"), ⟨25,by simp⟩ ⟩

inductive Project where | Pr1 | Pr2 deriving Repr
def Project.bind : Project → ProjectAttrs
| .Pr1 => ⟨ (600 : Nat) ⟩
| .Pr2 => ⟨ (700 : Nat) ⟩

-- тип, собирающий все сущности
inductive Entity where
| dept (d : Department)
| empl (e : Employee)
| proj (p : Project)
def Entity.bind : Entity → EntityAttrs
| dept d => .dept d.bind
| empl e => .empl e.bind
| proj p => .proj p.bind


--== Связи ==------------------------------------

-- тактики для автоматического доказательства кардинальности связей

syntax "proveIs1N" : tactic
macro_rules
| `(tactic| proveIs1N) =>
  `(tactic|
    intros a b c x y;
    cases a <;> cases b <;> cases c <;> cases x <;> cases y <;> simp)
syntax "proveIs11" : tactic
macro_rules
| `(tactic| proveIs11) =>
  `(tactic|
    intros a b c d;
    cases a <;> cases b <;> cases c <;> cases d <;>
    and_intros <;> intro x y <;> cases x <;> cases y <;> simp)

-- Связь "работники департамента" --

-- исходное отношение
inductive Dept_Empl : REL Department Employee where
| de1 : Dept_Empl «Трансп.цех» «Джон Доу»
| de2 : Dept_Empl «Трансп.цех» «Мэри Кью»
| de3 : Dept_Empl «ОК» «Мэри Энн»
open Dept_Empl

-- Dept_Empl вместе с условием 1:N
def Dept_Empl1N : REL_1N Department Employee where
  val := Dept_Empl
  property := by proveIs1N


-- роли (определяются относительно отношения)

def Dept_Empl.«место работы» (_ : Dept_Empl d e) : Department := d
def Dept_Empl.«работник»     (_ : Dept_Empl d e) : Employee   := e

-- примеры
example : Dept_Empl.de1.«работник» = «Джон Доу» := rfl
example : Dept_Empl.de1.«место работы» = «Трансп.цех» := rfl

-- тип работников департамента d (тип, зависящий от d)
def «работник департамента» (d : Department) : Type := { e : Employee // Dept_Empl d e }

-- тип рабочих мест сотрудника e (тип, зависящий от e)
def workplace (e : Employee) := { d : Department // Dept_Empl d e }

#check workplace «Джон Доу»
example : workplace «Джон Доу» := ⟨«Трансп.цех»,by constructor⟩

-- теорема: у каждого работника только одно место работы
theorem t1 : ∀ (e : Employee) (d1 d2 : Department), Dept_Empl d1 e → Dept_Empl d2 e → d1 = d2 := by
  apply Dept_Empl1N.property

-- тип коллег сотрудника e (работающие в том же департаменте)
def workmate (e : Employee) := { e' : Employee // ∃ d, Dept_Empl d e ∧ Dept_Empl d e'}

example : workmate «Джон Доу» := ⟨ «Мэри Кью», ⟨«Трансп.цех», Dept_Empl.de1, Dept_Empl.de2⟩ ⟩
example : workmate «Джон Доу» := ⟨ «Мэри Кью», by refine Exists.intro «Трансп.цех» ?_
                                                  and_intros <;> constructor ⟩
example : workmate «Джон Доу» := ⟨ «Мэри Кью», by constructor
                                                  case w => exact «Трансп.цех»
                                                  case h => and_intros <;> constructor ⟩


-- Связь "Начальник-подчинённый" (employee-dependents) -----------------------------------------

inductive Empl_Dep : REL Employee Employee where
| ed1 : Empl_Dep «Мэри Кью» «Джон Доу»
| ed2 : Empl_Dep «Мэри Кью» «Мэри Энн»

def Empl_Dep1N : REL_1N Employee Employee := ⟨Empl_Dep,by proveIs1N⟩

-- роли
def Empl_Dep.«начальник» (_ : Empl_Dep e1 e2) : Employee := e1
def Empl_Dep.«подчинённый» (_ : Empl_Dep e1 e2) : Employee := e2

-- тип подчинённых работника e
def «подчинённые» (e : Employee) : Type := { e' : Employee // Empl_Dep e e' }
example : «подчинённые» «Мэри Кью» := ⟨«Джон Доу», .ed1⟩


-- Связь "проект-исполнители" ----------------------------------------------

inductive Proj_Worker : REL Project Employee where
| pw1 : Proj_Worker .Pr1 «Джон Доу»
| pw2 : Proj_Worker .Pr1 «Мэри Кью»
| pw3 : Proj_Worker .Pr2 «Мэри Энн»

def Proj_Worker1N : REL_1N Project Employee where
  val := Proj_Worker
  property := by proveIs1N

-- роли
def Proj_Worker.«проект» (_ : Proj_Worker p e) : Project := p
def Proj_Worker.«участник проекта» (_ : Proj_Worker p e) : Employee := e

-- руководитель-проекты -------

inductive Manager_Proj : REL Employee Project where
| mp1 : Manager_Proj «Мэри Кью» .Pr1
| mp2 : Manager_Proj «Джон Доу» .Pr2

def Manager_Proj11 : REL_11 Employee Project where
  val := Manager_Proj
  property := by proveIs11

def Manager_Proj.«рук.проекта» (_ : Manager_Proj e p) : Employee := e
def Manager_Proj.«проект» (_ : Manager_Proj e p) : Project := p

--------------------------------
-- собираем отношения в один тип

inductive Relationship where
| de (r : Dept_Empl d e)    : Relationship
| ed (r : Empl_Dep e d)     : Relationship
| pw (r : Proj_Worker p e)  : Relationship
| mp (r : Manager_Proj e p) : Relationship
open Relationship

example : Relationship := .de .de1
example : Relationship := .pw .pw2

def Relationship.«место работы» : (r : Relationship) → Option Department
| @de d _ _ => some d
| _ => none

#reduce (Relationship.de .de1).«место работы»
example : (Relationship.de .de1).«место работы» = some «Трансп.цех» := rfl

#reduce (de .de3).«место работы»
example : (de .de3).«место работы» = some «ОК» := rfl

#reduce (pw .pw3).«место работы»
example : (pw .pw3).«место работы» = none := rfl
