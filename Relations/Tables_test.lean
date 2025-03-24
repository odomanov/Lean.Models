-- пример использования Tables.
import Relations.Tables

-- сначала определяем переменные DBType и asType для Tables
inductive DBType where
  | int | string | bool
deriving BEq, Repr

abbrev asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool

instance {t : DBType} : Repr (asType t) where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec

def beq (t : DBType) (x y : asType t) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y

instance {t : DBType} : BEq (asType t) where
  beq := beq t

-- перекодируем типы и функции из Tables.
-- (это должно бы делаться автоматически, как в Агде)
abbrev Column : Type := Tables.Column DBType
abbrev Schema : Type := Tables.Schema DBType
abbrev Subschema : Schema → Schema → Type := Tables.Subschema DBType
abbrev Row : Schema → Type := Tables.Row DBType asType
abbrev Table : Schema → Type := Tables.Table DBType asType
abbrev HasCol : Schema → String → DBType → Type := Tables.HasCol DBType
def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema :=
  Tables.Schema.renameColumn DBType

----------------------------------------
-- примеры таблиц
abbrev peak : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"elevation", .int⟩,
  ⟨"lastVisited", .int⟩
]
#eval peak

def mountainDiary : Table peak := [
  ("Mount Nebo",       "USA",     3637, 2013),
  ("Moscow Mountain",  "USA",     1519, 2015),
  ("Himmelbjerget",    "Denmark",  147, 2004),
  ("Mount St. Helens", "USA",     2549, 2010)
]
#eval mountainDiary

abbrev waterfall : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"lastVisited", .int⟩
]

def waterfallDiary : Table waterfall := [
  ("Multnomah Falls", "USA", 2018),
  ("Shoshone Falls",  "USA", 2014)
]
#eval waterfallDiary

abbrev travelDiary : Schema :=
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]

-- примеры подсхем

example : Subschema travelDiary peak :=
  .cons .here
    (.cons (.there .here)
      (.cons (.there (.there (.there .here))) .nil))

example : Subschema [] peak := by constructor

example : Subschema [⟨"location", .string⟩] peak := by repeat constructor
example : Subschema travelDiary peak := by repeat constructor

example : Subschema travelDiary waterfall := by repeat constructor
