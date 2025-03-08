-- ATC -- авиационный диспетчер

-- experience level
inductive ExpLevel : Type
| A | B | C

inductive Location : Type
| Front | Center
open Location

--def Aircraft : Type := Nat

structure DutyStation : Type where
  Capacity : Nat
  location : Location

--def Date : Type := Nat

structure OnDutyController : Type where
  LoginTime : String --Date
  Station : DutyStation

structure OffDutyController : Type where
  LastShiftEnded : String --Date

inductive DutyInfo : Type
| on_duty : OnDutyController → DutyInfo
| off_duty : OffDutyController → DutyInfo
open DutyInfo

structure ATC : Type where
  EmployeeID : String
  Rating : ExpLevel
  Duty : DutyInfo
open ATC

structure ControlZone : Type where
  Controller : ATC
  Traffic : Nat

inductive Duration : Type
| day | week

structure Shift : Type where
  MaxShift : Duration
  MinBreak : Duration

def DS1 : DutyStation := { Capacity := 20, location := Front }
def DS2 : DutyStation := { Capacity := 45, location := Front }
def DS3 : DutyStation := { Capacity := 30, location := Center }
def Gwen : ATC :=
  { EmployeeID := "ATC67"
  , Rating := ExpLevel.B
  , Duty := on_duty { LoginTime := "10:00", Station := DS1 }
  }
def Toshico : ATC :=
  { EmployeeID := "ATC53"
  , Rating := ExpLevel.A
  , Duty := on_duty { LoginTime := "11:00", Station := DS1 }
  }
def Ianto : ATC :=
  { EmployeeID := "ATC51"
  , Rating := ExpLevel.C
  , Duty := off_duty { LastShiftEnded := "12:00" }
  }

def OAK21C : ControlZone := { Controller := Toshico, Traffic := 15 }
def SFO37B : ControlZone := { Controller := Gwen, Traffic := 25 }
def SJC18C : ControlZone := { Controller := Toshico, Traffic := 30 }

def isOnDuty (c : ATC) : Bool :=
  match c with
  | ATC.mk _ _ (on_duty _) => true
  | _ => false

-----------------------------------------------------------------------------------
namespace Event

class State : Type
  state

class Event : Type
  event

class Transition : Type
  transition

end Event
