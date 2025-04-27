-- Entity–relationship model -- стандарт
-- Формализация без оглядки на моедли ER, RA и пр.

namespace ER

-- тип бинарных отношений (связей) между типами A и B
abbrev REL (A B : Type) : Type := A → B → Prop

-- типы связей 1:1, 1:N, N:1, N:N

-- 1:N
abbrev Is1N (R : REL A B) : Prop := ∀ a b c, R b a → R c a → b = c
abbrev REL_1N (A B : Type) : Type := {R : REL A B // Is1N R}

-- N:1
abbrev IsN1 (R : REL A B) : Prop := ∀ a b c, R a b → R a c → b = c
abbrev REL_N1 (A B : Type) : Type := {R : REL A B // IsN1 R}

-- 1:1
abbrev Is11 (R : REL A B) : Prop := ∀ a b c d, (R a c → R a d → c = d) ∧ (R a c → R b c → a = b)
abbrev REL_11 (A B : Type) : Type := {R : REL A B // Is11 R}

-- N:N  (нет условия)
abbrev REL_NN (A B : Type) : Type := REL A B

end ER
