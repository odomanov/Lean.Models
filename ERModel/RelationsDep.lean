-- Entity–relationship model
-- Определения для отношений/связей с зависимыми типами

namespace DepRel
-- "атрибуты" отношения
structure RELs (A B : Type) where
  left  : A
  right : B
deriving BEq, Repr

variable
  {atta : α} {attb : β}
  (A : α → Type) (B : β → Type)
  (R : {atta : α} → {attb : β} → RELs (A atta) (B attb) → Type)
  {r : RELs (A atta) (B attb)}

def Rel := {atta : α} → {attb : β} → RELs (A atta) (B attb) → Type

abbrev left  (_ : R r) : A atta := r.left
abbrev right (_ : R r) : B attb := r.right

-- типы связей 1:1, 1:N, N:1, N:N

-- 1:N
abbrev Is1N : Prop := ∀ (attax attay : α) (attb : β)
  (relx : RELs (A attax) (B attb)) (rely : RELs (A attay) (B attb))
  (x : R relx) (y : R rely),
  right A B R x = right A B R y → HEq relx.left rely.left
abbrev Rel_1N := { R : Rel A B // Is1N A B R }

syntax "proveIs1N" : tactic
macro_rules
| `(tactic| proveIs1N) =>
  `(tactic|
    -- intro attax attay attb relx rely x y eq <;>
    unfold Is1N;
    intros; rename_i x y _ <;>
    cases x <;> cases y <;> trivial)

-- N:1
abbrev IsN1 : Prop := ∀ (atta : α) (attbx attby : β)
  (relx : RELs (A atta) (B attbx)) (rely : RELs (A atta) (B attby))
  (x : R relx) (y : R rely),
  left A B R x = left A B R y → HEq relx.right rely.right
abbrev Rel_N1 := { R : Rel A B // IsN1 A B R }

syntax "proveIsN1" : tactic
macro_rules
| `(tactic| proveIsN1) =>
  `(tactic|
    -- intro atta attbx attby relx rely x y eq <;>
    unfold IsN1;
    intros; rename_i x y _ <;>
    cases x <;> cases y <;> trivial)

-- 1:1
abbrev Is11 : Prop := Is1N A B R ∧ IsN1 A B R
abbrev Rel_11 := { R : Rel A B // Is11 A B R }

syntax "proveIs11" : tactic
macro_rules
| `(tactic| proveIs11) =>
  `(tactic| and_intros; proveIs1N; proveIsN1)

-- N:N  (нет условия)
abbrev IsNN : Prop := True
abbrev Rel_NN := { R : Rel A B // IsNN }

end DepRel
