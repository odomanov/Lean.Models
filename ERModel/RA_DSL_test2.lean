-- тест для DSL реляционной алгебры
import ERModel.RA
import ERModel.RA_DSL
-- import Lib.Alldecls

RAModel RA1 where
  DBTypes
    (int => Int)
    (nat => Nat)
    (string => String)
    (bool => Bool)
  Tables
    peak
    ("name" : string)
    ("location" : string)
    ("elevation" : nat)
    ("lastVisited" : nat)
    mountainDiary
      {("Mount Nebo",       "USA",     (3637 : Nat), (2013 : Nat))}
      {("Moscow Mountain",  "USA",     (1519 : Nat), (2015 : Nat))}
      {("Himmelbjerget",    "Denmark",  (147 : Nat), (2004 : Nat))}
      {("Mount St. Helens", "USA",     (2549 : Nat), (2010 : Nat))}
  Tables
    waterfall
    ("name" : string)
    ("location" : string)
    ("lastVisited" : nat)
    waterfallDiary
      {("Multnomah Falls", "USA", (2018 : Nat))}
      {("Shoshone Falls",  "USA", (2014 : Nat))}
  Tables
    loc
    ("location" : string)
    locations
      {("Some location")}
      {("Another location")}
  endRAModel


#check RA1.DBType
open RA1
#check DBType.asType
#check DBType.string.asType
#reduce DBType.string.asType

#check Tables.Schema
#check RA1.Schema
#check Schema
#check Table
#check Column
#check waterfall
#eval waterfall
#eval waterfallDiary
#eval locations


-- #alldecls
