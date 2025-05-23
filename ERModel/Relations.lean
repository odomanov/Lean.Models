-- Entity–relationship model -- стандарт
-- Определения для отношений/связей

namespace Relations

-- тип бинарных отношений (связей) между типами A и B
abbrev Rel (α β : Type) : Type := α → β → Prop

-- типы связей 1:1, 1:N, N:1, N:N

-- 1:N
abbrev Is1N (R : Rel α β) : Prop := ∀ a b c, R b a → R c a → b = c
abbrev Rel_1N (α β : Type) : Type := {R : Rel α β // Is1N R}

syntax "proveIs1N" : tactic
macro_rules
| `(tactic| proveIs1N) =>
  `(tactic|
    intros a b c; intros;
    cases a <;> cases b <;> cases c <;> simp <;> contradiction)

-- N:1
abbrev IsN1 (R : Rel α β) : Prop := ∀ a b c, R a b → R a c → b = c
abbrev Rel_N1 (α β : Type) : Type := {R : Rel α β // IsN1 R}

syntax "proveIsN1" : tactic
macro_rules
| `(tactic| proveIsN1) =>
  `(tactic|
    intro a b c x y;
    cases a <;> cases b <;> cases c <;>
    cases x <;> cases y <;> trivial)

-- 1:1
abbrev Is11 (R : Rel α β) : Prop := ∀ a b c d, (R a c → R a d → c = d) ∧ (R a c → R b c → a = b)
abbrev Rel_11 (α β : Type) : Type := {R : Rel α β // Is11 R}

syntax "proveIs11" : tactic
macro_rules
| `(tactic| proveIs11) =>
  `(tactic|
    intro a b c d; and_intros <;>
    intros <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp <;> contradiction
    -- intros a b c d; intros;
    -- cases a <;> cases b <;> cases c <;> cases d <;> simp <;> contradiction
    )

-- N:N  (нет условия)
abbrev Rel_NN (α β : Type) : Type := { R : Rel α β // True }


-- конкретные связи: объекты a b + док-во, что между ними есть связь.
-- Это тип пар объектов, находящихся в отношении R.
-- Если REL это отношение, заданное как предикат, то PRel -- это то же отношение,
--   но в виде структуры (т.е. пар).
structure SRel (R : Rel α β) where
  src : α
  tgt : β
  prf : R src tgt := by simp!
deriving Repr


-- конкретизации SRel для 1:1, 1:N,...
abbrev SRel_1N (R : Rel_1N A B) := SRel R.val
abbrev SRel_N1 (R : Rel_N1 A B) := SRel R.val
abbrev SRel_11 (R : Rel_11 A B) := SRel R.val
abbrev SRel_NN (R : Rel_NN A B) := SRel R.val

end Relations
