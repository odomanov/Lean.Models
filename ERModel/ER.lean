/- Entity–relationship model
   1. Сущности
   2. Связи (1:1, 1:N, N:1, N:N) -- только бинарные
   3. Атрибуты -- для сущности или для связи
   4. Роли -- формализуются при использовании (не в этом файле)

   В модели различаются идентификаторы и их значения.
   Aᵢ, Bᵢ это типы идентификаторов, а A, B -- типы соответствующих им значений.
   Функции bind, bindA, bindB связывают идентификаторы со значениями (см.пример).
   При использовании модели должны быть заданы типы идентификаторов, значений и
   функции связывания bind.
-/

namespace ER
variable
  {Aᵢ A Bᵢ B : Type}
  (bindA : Aᵢ → A)
  (bindB : Bᵢ → B)

-- тип бинарных отношений (связей) между типами A и B
abbrev REL (A B : Type) : Type := A → B → Prop

-- функция как бинарное отношение
def graph (f : A → B) : REL A B := fun x y => f x = y

-- Не всем элементам типа значений может соответствовать идентификатор.
-- Функция mkE выделяет подтип A тех элементов, которые имеют идентификаторы.
-- Элементы этого типа представляют собой кортежи из элемента A, соответствующего идентификатора
-- из Aᵢ и доказательства того, что они связаны функцией bind.
abbrev mkE (bind : Aᵢ → A) : Type := Σ (x : A), Σ' (xᵢ : Aᵢ), graph bind xᵢ x

-- функции перевода из Aᵢ в mkE и обратно
def XᵢtoX (bind : Aᵢ → A) : Aᵢ → mkE bind := fun xᵢ => ⟨bind xᵢ, xᵢ, rfl⟩
def XtoXᵢ (bind : Aᵢ → A) : mkE bind → Aᵢ := fun x => x.snd.fst

-- Функции NNN.bind переносят тип NNN, заданный на идентификаторах, в тип NNN,
-- заданный на значениях (т.е. на mkE..).

-- перенос функции
def Fun.bind (f : Aᵢ → Bᵢ) : mkE bindA → mkE bindB :=
  XᵢtoX bindB ∘ f ∘ XtoXᵢ bindA

-- перенос отношения
def REL.bind : REL Aᵢ Bᵢ → REL (mkE bindA) (mkE bindB) :=
  fun R => fun x y => R (x.snd.fst) (y.snd.fst)

-- перенос отношения в обратную сторону
def REL.inv : REL (mkE bindA) (mkE bindB) → REL Aᵢ Bᵢ :=
  fun R => fun x y => R ⟨bindA x, x, rfl⟩ ⟨bindB y, y, rfl⟩


-- типы связей 1:1, 1:N, N:1, N:N

-- 1:N
abbrev Is1N (R : REL A B) : Prop := ∀ a b c, R b a → R c a → b = c
abbrev REL_1N (A B : Type) : Type := { R : REL A B // Is1N R }

-- TODO: prove
axiom ax1N : (rᵢ : REL Aᵢ Bᵢ) → (isᵢ : Is1N rᵢ) → Is1N (REL.bind bindA bindB rᵢ)

def REL_1N.bind : REL_1N Aᵢ Bᵢ → REL_1N (mkE bindA) (mkE bindB) :=
  fun r => ⟨REL.bind bindA bindB r.val, ax1N bindA bindB r.val r.property⟩

-- N:1
abbrev IsN1 (R : REL A B) : Prop := ∀ a b c, R a b → R a c → b = c
abbrev REL_N1 (A B : Type) : Type := { R : REL A B // IsN1 R }

-- TODO: prove
axiom axN1 : (ri : REL Aᵢ Bᵢ) → (isi : IsN1 ri) → IsN1 (REL.bind bindA bindB ri)

def REL_N1.bind : REL_N1 Aᵢ Bᵢ → REL_N1 (mkE bindA) (mkE bindB) :=
  fun r => ⟨REL.bind bindA bindB r.val, axN1 bindA bindB r.val r.property⟩

-- 1:1
abbrev Is11 (R : REL A B) : Prop := ∀ a b c d, R a c → R a d → c = d ∧ R a c → R b c → a = b
abbrev REL_11 (A B : Type) : Type := {R : REL A B // Is11 R}

-- TODO: prove
-- Должно доказываться?
axiom ax11 : (ri : REL Aᵢ Bᵢ) → (isi : Is11 ri) → Is11 (REL.bind bindA bindB ri)

def REL_11.bind : REL_11 Aᵢ Bᵢ → REL_11 (mkE bindA) (mkE bindB) :=
  fun r => ⟨REL.bind bindA bindB r.val, ax11 bindA bindB r.val r.property⟩

-- N:N  (нет условия)
abbrev REL_NN (A B : Type) : Type := REL A B
def REL_NN.bind := REL.bind bindA bindB


-- конкретные связи: объекты a b + док-во, что между ними есть связь.
-- Это тип пар объектов, находящихся в отношении R.
-- Если REL это отношение, заданное как предикат, то Rel -- это то же отношение,
--   но в виде структуры (т.е. пар).
structure Rel (R : REL A B) where
  src : A
  tgt : B
  prf : R src tgt := by simp!
deriving Repr

def Rel.bind (R : REL Aᵢ Bᵢ) : Rel R → Rel (R.bind bindA bindB) :=
  fun r => { src := XᵢtoX bindA r.src
           , tgt := XᵢtoX bindB r.tgt
           , prf := r.prf
           }

-- конкретизации Rel для 1:1, 1:N,...
abbrev Rel_1N (R : REL_1N A B) := Rel R.val
abbrev Rel_N1 (R : REL_N1 A B) := Rel R.val
abbrev Rel_11 (R : REL_11 A B) := Rel R.val
abbrev Rel_NN (R : REL_NN A B) := Rel R

abbrev Rel_1N.bind (R : REL_1N Aᵢ Bᵢ) := Rel.bind bindA bindB R.val
abbrev Rel_N1.bind (R : REL_N1 Aᵢ Bᵢ) := Rel.bind bindA bindB R.val
abbrev Rel_11.bind (R : REL_11 Aᵢ Bᵢ) := Rel.bind bindA bindB R.val
abbrev Rel_NN.bind (R : REL_NN Aᵢ Bᵢ) := Rel.bind bindA bindB R

end ER
