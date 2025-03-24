import Relations.LimitList
open LimitList

example : LimList Nat 0 1 := ⟦1⟧
example : LimList Nat 0 500 := ⟦⟧
example : LimList Nat 0 2 := ⟦1,5⟧
example : LimList Nat 1 4 := ⟦1,2⟧
example : LimList Nat 1 4 := ⟦ 1,2,6,7 ⟧
-- example : LimList Nat 1 4 := ⟦ ⟧                  -- не удовлетворяет ограничениям
-- example : LimList Nat 1 4 := ⟦ 1,2,6,7,9 ⟧        -- не удовлетворяет ограничениям

example : LimList Nat 0 ⋆ := ⟦⟧
-- example : LimList Nat 1 ⋆ := ⟦⟧           -- не удовлетворяет ограничениям
example : LimList Nat 0 ⋆ := ⟦ 10,23,4,7,90,11,34,567,34,98⟧

example : LimList String 1 1 := ⟦ "лорпо" ⟧
example : LimList String 0 5 := ⟦⟧
example : LimList String 0 5 := ⟦"ыгпрл", "щкшгеко", "лорв", "впрл", "рлавор"⟧
