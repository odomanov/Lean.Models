# Entity-relationship Model

Формализация ER-моделей в Lean. Первое приближение.

+ [ER](ER.lean) — Модель 
+ [ER_test](ER_test.lean) — Пример использования
+ [ER_DSL](ER_DSL.lean) — DSL для ER-моделей
+ [ER_DSL_test](ER_DSL_test.lean) — пример использования

## Реляционные алгебры

+ [RA](RA.lean) — Определения для реляционных алгебр
+ [RA_DSL](RA_DSL.lean) — DSL для реляционных алгебр (пока только
  определение таблиц)
+ [RA_DSL_test](RA_DSL_test.lean) — пример использования 
+ [RA_DSL_test2](RA_DSL_test2.lean) — ещё пример использования 

## Преобразование ER-моделей в RA-модели

+ [ER2RA](ER2RA.lean) — Преобразование моделей. Делается чисто
  синтаксическим путём.
+ [ER2RA_test](ER2RA_test.lean) — пример: модель из `ER_test` преобразуется
  в модель из `RA_test`.
