-- ATC -- авиационный диспетчер
-- минимальная теория: диспетчеры и дежурные станции
import ATC.Situation

inductive Action : Type
| take_station : DutyStation → Action
| release_station : Action

-- состояния диспетчера
inductive State : Type
| on_duty : DutyStation → Time → State    -- дежурит на станции
| off_duty : LastShiftEnded → State       -- свободен
deriving Repr
open State

-- activity for State
-- (полагаем, что функция есть, но для простоты не определяем её)
axiom StateToAction : State → List Action

-- диспетчер с состоянием (дежурный/свободен)
structure ATC extends ATC.Info.Info where
  state : State
deriving Repr

def Gwen    : ATC := ⟨ATC.Info.Gwen,    off_duty (0 : Time)⟩
def Toshico : ATC := ⟨ATC.Info.Toshico, off_duty (0 : Time)⟩
def Ianto   : ATC := ⟨ATC.Info.Ianto, on_duty DS1 (0 : Time)⟩

-- TODO: автоматизировать
def ATCs : List ATC := [Gwen, Toshico, Ianto]

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
example : Gwen.isOffDuty := by trivial  --True.intro

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

-- события
inductive Event : Type
| login : DutyStation → Time → Event
| logout : Time → Event

-- тип переходов между состояниями по событию
inductive Move : State → Event → State → Prop
| m1 (s : DutyStation) (t0 t : Time) {tt : t0 ≤ t} :
  Move (off_duty t0) (Event.login s t) (on_duty s t)
| m2 (s : DutyStation) (t0 t : Time) {tt : t0 ≤ t} :
  Move (on_duty s t0) (Event.logout t) (off_duty t)

-- в любое время toff позже ton диспетчер со станции DS1 может выйти
theorem t2 : ∀ ton toff, (ton ≤ toff) →  Move (on_duty DS1 ton) (Event.logout toff) (off_duty toff) :=
  -- fun tt => @Move.m2 DS1 tt
  by intros
     apply Move.m2 DS1
     assumption

-- пропозиция "станция занята"
def busy (s : DutyStation) : Prop :=
  ∃ (c : ATC), ∃ t, c.state = on_duty s t

-- станция DS1 занята
theorem b1 : busy DS1 := Exists.intro Ianto (Exists.intro 0 rfl)

-- тип занятых станций
structure onDutyS where
  station : DutyStation
  busy : busy station

-- DS1 занята (относится к типу занятых станций)
example : onDutyS := ⟨ DS1, b1 ⟩
