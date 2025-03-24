import Relations.LimitList
import Relations.StringType
open LimitList StringType

-- "классы"
structure Organization where
  name    : (LimList (Str 0 100) 1 1)
  address : (LimList (Str 5 300) 1 5)

structure Person where
  name       : (LimList (Str 5) 1 1)
  work_place : (LimList Organization 0 ⋆)

-- примеры классов
def org1 : Organization where
  name:=    ⟦ (str "Завод" "pattern" : Str 0 100) ⟧
  address:= ⟦ (str "г.Далёкий" "pattern" : Str 5 300) ⟧

def org2 : Organization where
  name:=    ⟦(str "Компания" "pattern" : Str 0 100)⟧
  address:= ⟦(str "п.Близкий" "pattern" : Str 5 300),
             (str "о.Пальма" "pattern" : Str 5 300)⟧

def Ivanov : Person := ⟨ ⟦(str "Иванов" "pattern" : Str 5)⟧, ⟦org1⟧ ⟩
def Petrov : Person := ⟨ ⟦(str "Петров" "pattern" : Str 5)⟧, ⟦org2⟧ ⟩
def Bender : Person where
  name := ⟦(str "Бендер-бей" "pattern" : Str 5)⟧
  work_place := ⟦⟧
