-- ATC -- авиационный диспетчер
-- минимальная модель: диспетчеры и дежурные станции
import ATC.Situation

-- состояния диспетчера
inductive ATC.State : Type
| on_duty : DutyStation → Time → ATC.State    -- дежурит на станции
| off_duty : LastShiftEnded → ATC.State       -- свободен
deriving Repr
open ATC.State

-- действия при переходе в состояние
inductive Action : Type
| take_station : DutyStation → Action    -- занять станцию
| release_station : Action               -- освободить станцию

-- activity for State (список действий при входе в состояние)
-- (полагаем, что функция есть, но для простоты не определяем её)
axiom StateToAction : ATC.State → List Action

-- диспетчер с состоянием (дежурный/свободен)
structure ATC extends ATC.Info where
  state : ATC.State
deriving Repr

def Gwen    : ATC := ⟨ATC.Info.Gwen,    off_duty (0 : Time)⟩
def Toshico : ATC := ⟨ATC.Info.Toshico, off_duty (0 : Time)⟩
def Ianto   : ATC := ⟨ATC.Info.Ianto, on_duty DS1 (0 : Time)⟩

-- Список диспетчеров.
-- TODO: автоматизировать
def ATCs : List ATC := [Gwen, Toshico, Ianto]

-- станция, на которой дежурит диспетчер c
def station : (c : ATC) → Option DutyStation
| ⟨ _, on_duty ds _ ⟩ => some ds
| _ => none

#eval station Ianto
#eval station Gwen

-- диспетчер, дежурящий на станции ds
def controller (ds : DutyStation) : Option ATC :=
  List.find? p ATCs
  where p : ATC → Bool
  | ⟨ _, on_duty s _ ⟩ => if s == ds then true else false
  | _ => false

#eval controller DS1
#eval controller DS2

-- пропозиция "ATC на дежурстве"
def ATC.isOnDuty (c : ATC) : Prop :=
  ∃ ds, ∃ t, c.state = on_duty ds t

-- пропозиция "ATC свободен"
-- (другой способ определения)
def ATC.isOffDuty (c : ATC) : Prop :=
  match c with
  | .mk (state := (off_duty ..)) .. => True
  | _ => False

-- докажем, что Gwen свободен
example : Gwen.isOffDuty := by trivial

-- докажем, что Ianto дежурит
theorem t0 : Ianto.isOnDuty :=
  Exists.intro DS1 (Exists.intro (0 : Time) rfl)

-- тип диспетчеров на дежурстве (диспетчер + док-во его дежурства)
structure onDutyATC extends ATC where
  isOnDuty : toATC.isOnDuty
deriving Repr

-- тип свободных диспетчеров
structure offDutyATC extends ATC where
  isOffDuty : toATC.isOffDuty
deriving Repr

-- Gwen свободен (принадлежит типу offDutyATC)
example : offDutyATC := ⟨ Gwen, True.intro ⟩

-- Ianto дежурит (принадлежит типу onDutyATC)
example : onDutyATC := ⟨ Ianto, t0 ⟩

-- пропозиция "станция занята"
def busy (s : DutyStation) : Prop :=
  List.any ATCs p = true
  where p : ATC → Bool := fun x =>
    match x.state with
    | on_duty ds _ => if ds == s then true else false
    | off_duty _ => false

-- станция DS1 занята
theorem ds1_busy : busy DS1 := by trivial

-- тип занятых станций
structure onDutyS where
  station : DutyStation
  busy : busy station

-- DS1 занята (относится к типу занятых станций)
example : onDutyS := ⟨ DS1, ds1_busy ⟩

-- пропозиция "станция свободна" (= "неверно, что станция занята")
def free (s : DutyStation) : Prop := ¬ busy s

-- станция DS2 свободна
theorem ds2_free : free DS2 := by intro; contradiction
-- станция DS1 не свободна
theorem ds1_not_free : ¬ free DS1 := by intro; trivial

-- события
inductive Event : Type
| login : DutyStation → Time → Event
| logout : Time → Event

-- Тип переходов между состояниями по событию.
-- m1, m2 определяют, какие переходы возможны.
-- m1 = "по событию login свободный диспетчер переходит в состояние дежурства".
-- m2 = "по событию logout дежурный диспетчер освобождается".
-- Условие tt определяет последовательность времён.
inductive Move : State → Event → State → Prop
| m1 (s : DutyStation) (t0 t : Time) {tt : t0 ≤ t} :
  free s → Move (off_duty t0) (Event.login s t) (on_duty s t)
| m2 (s : DutyStation) (t0 t : Time) {tt : t0 ≤ t} :
  Move (on_duty s t0) (Event.logout t) (off_duty t)

-- в любое время toff позже ton диспетчер со станции DS1 может выйти
theorem t2 : ∀ ton toff, (ton ≤ toff) →  Move (on_duty DS1 ton) (Event.logout toff) (off_duty toff) :=
  -- fun tt => @Move.m2 DS1 tt
  by intros
     apply Move.m2 DS1
     assumption

-- в любое время toff позже ton диспетчер может войти на станцию DS2
theorem t3 : ∀ ton toff, (ton ≤ toff) →  Move (off_duty ton) (Event.login DS2 toff) (on_duty DS2 toff) :=
  by intros
     have h := ds2_free
     apply Move.m1 DS2
     assumption
     assumption
