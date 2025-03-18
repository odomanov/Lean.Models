-- трансформация Classes в Tables
-- import Lean.Elab.Command
import Relations.Classes
import Relations.Tables

-- подготовка переменных Tables из Classes
abbrev DBType : Type := Classes.DataType
namespace DBType
export Classes.DataType (string num bool props ref cls)
end DBType
abbrev asType : DBType → Type := Classes.asType

-- перекодируем данные из Tables и Classes
abbrev Column : Type := Tables.Column DBType
abbrev Schema : Type := Tables.Schema DBType
abbrev Subschema : Schema → Schema → Type := Tables.Subschema DBType
abbrev Row : Schema → Type := Tables.Row DBType asType
abbrev Table : Schema → Type := Tables.Table DBType asType
abbrev HasCol : Schema → String → DBType → Type := Tables.HasCol DBType
def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema :=
  Tables.Schema.renameColumn DBType

abbrev ReferenceKind : Type := Classes.ReferenceKind
namespace Reference
export Classes.ReferenceKind (Association Composition Aggregation)
end Reference
abbrev Property : Type := Classes.Property
export Classes.Property (attr ref)
abbrev Attribute : Type := Classes.Attribute
abbrev Reference : Type := Classes.Reference
abbrev Class : Type := Classes.Class


-- подготовка таблиц

abbrev myclass : Schema := [
  -- ⟨"name", .string⟩,
  ⟨"property", .props⟩,
]

-- примеры таблиц

example : Table myclass := [
  ([attr ⟨.string⟩]),
]

example : Table myclass := [
  ([ref ⟨Reference.Association, ⟨[]⟩⟩] ),
  ([ref ⟨Reference.Association, ⟨[ attr ⟨.num⟩ ]⟩⟩] )
]
