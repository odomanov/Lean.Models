-- ATC -- авиационный диспетчер
-- Определение объектов модели: диспетчеров (ATC), дежурных станций
-- (DutyStation) и зон (Zone)
import Std.Time

-- рейтинг диспетчера
inductive ExpLevel : Type
| A | B | C
deriving Repr

-- местонахождение станции
inductive Location : Type
| Front | Center
deriving BEq, Repr

structure DutyStation : Type where
  capacity : Nat
  location : Location
deriving BEq, Repr

abbrev Time : Type := Std.Time.Timestamp
abbrev LastShiftEnded : Type := Time
deriving instance Repr for LastShiftEnded

namespace ATC.Info

-- информация о диспетчере
structure Info where
  employeeID : String
  rating : ExpLevel
deriving Repr

-- три диспетчера
def Gwen : Info := ⟨"ATC67", .B⟩
def Toshico : Info := ⟨"ATC53", .A⟩
def Ianto : Info := ⟨"ATC51", .C⟩

end ATC.Info

-- дежурные станции
def DS1 : DutyStation := ⟨20, .Front⟩
def DS2 : DutyStation := ⟨45, .Front⟩
def DS3 : DutyStation := ⟨30, .Center⟩

-- зоны контроля
structure ControlZone : Type where
  Traffic : Nat
deriving Repr

def OAK21C : ControlZone := { Traffic := 15 }
def SFO37B : ControlZone := { Traffic := 25 }
def SJC18C : ControlZone := { Traffic := 30 }
