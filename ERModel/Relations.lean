-- Entity–relationship model -- стандарт
-- Определения для отношений/связей
import Mathlib.Data.Rel

namespace ER

-- типы связей 1:1, 1:N, N:1, N:N α β

-- 1:N
abbrev Is1N (R : Rel α β) : Prop := ∀ a b c, R b a → R c a → b = c
abbrev Rel_1N (α β : Type) : Type := {R : Rel α β // Is1N R}

-- N:1
abbrev IsN1 (R : Rel α β) : Prop := ∀ a b c, R a b → R a c → b = c
abbrev Rel_N1 (α β : Type) : Type := {R : Rel α β // IsN1 R}

-- 1:1
abbrev Is11 (R : Rel α β) : Prop := ∀ a b c d, (R a c → R a d → c = d) ∧ (R a c → R b c → a = b)
abbrev Rel_11 (α β : Type) : Type := {R : Rel α β // Is11 R}

-- N:N  (нет условия)
abbrev Rel_NN (α β : Type) : Type := Rel α β

end ER
