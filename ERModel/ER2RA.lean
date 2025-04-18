-- Трансформация ER-модели в RA-модель
import Lean
import ERModel.ER_DSL_syntax
import ERModel.RA
import ERModel.RA_DSL
-- import Lib.Alldecls
open Lean Syntax
set_option linter.unusedVariables false

open RA_DSL
open ER_DSL

syntax "⟨" term,+ "⟩" : term

-- добавляем тип Entity по Items
private def mkEntIdent (acc : TSyntax `command) (e : TSyntax `entity) : MacroM (TSyntax `command) := do
  match e with
  | `(entity| $nm:ident $[($fld:ident : $fty:ident)]* Items $itm:ident* Binds $bnds*) =>
    let nmIdent := nm.suffix "Ident"
    let mkind ← `(command| inductive $nmIdent : Type where $[| $itm:ident]* deriving Repr, BEq)
    `($acc:command
      $mkind:command)
  | _ => Macro.throwError "ER2RA: mkEntIdent error"

-- Для создания таблиц связи DBType должен содержать типы для <entity>Ident. Добавляем их.
private def mkAttFromEnt (acc : TSyntaxArray `binding) (e : TSyntax `entity)
  : MacroM (TSyntaxArray `binding) := do
  match e with
  | `(entity| $nm:ident $[($fld:ident : $fty:ident)]* Items $itm:ident* Binds $bnds*) =>
    let nmDBT   := nm.suffix "DBT"
    let nmIdent := nm.suffix "Ident"
    let bnd ← `(binding| ($nmDBT => $nmIdent))
    let acc:= acc.push bnd
    pure acc
  | _ => Macro.throwError "ER2RA: mkAttFromEnt error"

-- создаём таблицу DBType
private def mkDBTypes (bnd : TSyntaxArray `binding) (es : TSyntaxArray `entity)
  : MacroM (TSyntaxArray `binding) := do
  let attrs ← es.foldlM mkAttFromEnt #[]      -- добавляем <entity>Ident
  let bnd := bnd.append attrs
  pure bnd

-- создаём кортежи значений для таблицы сущности
private def mkTbl (acc : TSyntaxArray `term) (tb : TSyntax `binding) : MacroM (TSyntaxArray `term) := do
  match tb with
  | `(binding| ($id:ident => ⟨ $val:term,* ⟩)) =>
    let line ← match val.getElems with
        | #[] => `((.$id))
        | v   => `((.$id, $v,*))
    let acc := acc.push line
    pure acc
  | _ => Macro.throwError "ER2RA: mkTbl error"

-- создаём таблицы для сущностей. Как первую колонку добавляем <entity>Ident
private def mkEnt (acc : TSyntaxArray `tablesblock) (e : TSyntax `entity)
  : MacroM (TSyntaxArray `tablesblock) := do
  match e with
  | `(entity| $nm:ident $[($fld:ident : $fty:ident)]* Items $itm:ident* Binds $bnds*) =>
    let schId := nm.suffix "Schema"
    let fldstr := fld.map (fun x => TSyntax.mk (mkStrLit x.getId.toString))
    let nmLit := TSyntax.mk (mkStrLit nm.getId.toString)
    let nmDBT := nm.suffix "DBT"
    let mksch ← `(schema| $schId:ident ($nmLit : $nmDBT) $[($fldstr : $fty)]*)
    let mktbls ← bnds.foldlM mkTbl $ #[]                      -- цикл по Binds
    let tbbb := #[← `(table| $nm:ident $[{ $mktbls }]*)]
    let schtbl ← `(tablesblock| Tables $mksch:schema $tbbb:table*)  -- блок Tables в RA-модели
    let acc := acc.push schtbl
    pure acc
  | _ => Macro.throwError "ER2RA: mkEnt error"

-- создаём таблицы для связей
private def mkRel (acc : TSyntaxArray `tablesblock) (r : TSyntax `relationship)
  : MacroM (TSyntaxArray `tablesblock) := do
  match r with
  | `(relationship| $e1:ident ($r1:ident) $e2:ident ($r2:ident) $rnam:ident $NN:str
      $[($left:ident → $right:ident)]*) =>
      let schId := rnam.suffix "Schema"   -- имя таблицы связи: добавляем "SChema"
      let e1DBT := e1.suffix "DBT"
      let e2DBT := e2.suffix "DBT"
      let toStrLit (x : TSyntax `ident) : TSyntax `str := TSyntax.mk (mkStrLit x.getId.toString)
      let mksch ← `(schema| $schId:ident ($(toStrLit e1) : $e1DBT) ($(toStrLit e2) : $e2DBT) )
      let tbbb := #[← `(table| $rnam:ident $[{(.$left, .$right)}]*)]
      let reltbl ← `(tablesblock| Tables $mksch:schema $tbbb:table*)  -- блок Tables в RA-модели
      let acc := acc.push reltbl
      pure acc
  | _ => Macro.throwError "ER2RA: mkRel error"


-- Основной макрос. Переводит DSL ER-модели в DSL RA-модели
macro_rules
| `(ermodel|
    ERModel $ns:ident where                     -- исходная содель
      Attributes $bnd:binding*
      Entities $es*
      Relationships $rs*
    endERModel) => do
    let mkidents ← es.foldlM mkEntIdent $ TSyntax.mk mkNullNode
    let dbtypes ← mkDBTypes bnd es        -- таблица типов DBType
    let enttbls ← es.foldlM mkEnt #[]     -- цикл по сущностям
    let reltbls ← rs.foldlM mkRel #[]     -- цикл по связям
    `($mkidents:command
      RAModel $ns:ident where                 -- RA-модель
        DBTypes $dbtypes:binding*
        $enttbls:tablesblock*
        $reltbls:tablesblock*
      endRAModel)

-- #alldecls
