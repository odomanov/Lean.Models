-- примеры использования NatType
import Relations.NatType
open NatType

example : NatL 5 := nat 7
example : NatL 5 25 := nat 10
example : NatL 5 25 := nat 5
-- example : NatL 5 25 := nat 30   -- не удовлетворяет ограничениям
-- example : NatL 5 25 := nat 1    -- не удовлетворяет ограничениям

abbrev N5 := NatL 5
abbrev N5!25 := NatL 5 25

example : N5 := nat 7
example : N5!25 := nat 10
example : N5!25 := nat 5
-- example : N5!25 := nat 30   -- не удовлетворяет ограничениям
-- example : N5!25 := nat 1    -- не удовлетворяет ограничениям
