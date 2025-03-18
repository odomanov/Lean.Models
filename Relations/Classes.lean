-- Модель классов

namespace Classes

-- наши типы данных
inductive DataType where
| string | num | bool | props | ref | cls
deriving BEq, Repr

-- соответствующие им типы Lean (соответствие см. ниже)
structure StringType where
  val : String
  length : Nat := 100
  minLength: Nat := 10
  maxLength : Nat := 1000
deriving BEq

structure NumericType where
  val : Nat
  size : Nat
  totalDigit : Nat
deriving BEq

structure BooleanType where
  val : Bool
deriving BEq

inductive ReferenceKind where
| Association | Composition | Aggregation
deriving BEq, Repr

-- классы и их свойства
mutual
  -- класс содержит список свойств
  structure Class where
    props : List Property

  -- свойство может быть либо атрибутом, либо ссылкой
  inductive Property where
  | attr : Attribute → Property
  | ref  : Reference → Property

  -- атрибут содержит только тип данных
  structure Attribute where
    datatype : DataType

  -- ссылка содержит её тип и класс, на который ссылаются
  structure Reference where
    kind : ReferenceKind
    ref : Class

end

-- перевод наших типов в типы Lean
def asType (dt : DataType) : Type :=
  match dt with
  | .string => StringType
  | .num => NumericType
  | .bool => BooleanType
  | .props => List Property
  | .ref => Reference
  | .cls => Class

-- примеры

def class1 : Class := ⟨[]⟩

example : Attribute := ⟨.bool⟩
example : Reference := ⟨ReferenceKind.Association, class1⟩
example : Property := Property.attr ⟨.num⟩
example : Property := Property.ref ⟨ReferenceKind.Association, class1⟩

def class2 : Class := ⟨[ Property.attr ⟨.bool⟩ ]⟩
def class3 : Class := ⟨[ Property.ref ⟨ReferenceKind.Association, class2⟩ ]⟩

end Classes
