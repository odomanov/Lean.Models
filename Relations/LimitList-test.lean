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
example : LimList Nat 0 ⋆ := ⟦ 10,23,4,7,90,11,34,567,34,98⟧ -- нет предела

example : LimList String 1 1 := ⟦ "лорпо" ⟧
example : LimList String 0 5 := ⟦⟧
example : LimList String 0 5 := ⟦"ыгпрл", "щкшгеко", "лорв", "впрл", "рлавор"⟧

theorem t0 : ∀ [BEq α] (L : List α), (0 < L.length) → ∃ x, x ∈ L := by
  intros A L p
  exists L.head (List.ne_nil_of_length_pos p)
  simp

theorem t1 : ∀ [BEq α] (L : LimList α 1 ⋆), ∃ x, x ∈ L.list := by
  intros eq L
  have m : 0 < L.list.length := by refine Nat.lt_of_succ_le L.lower_le
  apply t0 L.list m
