-- ATC -- авиационный диспетчер
-- исходная ситуация
import Std.Time

-- experience level
inductive ExpLevel : Type
| A | B | C
deriving Repr

inductive Location : Type
| Front | Center
deriving BEq, Repr
open Location

abbrev Time : Type := Std.Time.Timestamp

structure DutyStation : Type where
  capacity : Nat
  location : Location
deriving BEq, Repr

-- structure OnDutyController : Type where
--   LoginTime : String --Date
--   Station : DutyStation

-- structure OffDutyController : Type where
--   LastShiftEnded : String --Date

abbrev LastShiftEnded : Type := Time
deriving instance Repr for LastShiftEnded

namespace ATC.Info
structure Info where
  employeeID : String
  rating : ExpLevel
deriving Repr

def Gwen : Info := ⟨"ATC67", .B⟩
def Toshico : Info := ⟨"ATC53", .A⟩
def Ianto : Info := ⟨"ATC51", .C⟩

end ATC.Info

def DS1 : DutyStation := ⟨20, Front⟩
def DS2 : DutyStation := ⟨45, Front⟩
def DS3 : DutyStation := ⟨30, Center⟩

structure ControlZone : Type where
  Traffic : Nat
deriving Repr

def OAK21C : ControlZone := { Traffic := 15 }
def SFO37B : ControlZone := { Traffic := 25 }
def SJC18C : ControlZone := { Traffic := 30 }
