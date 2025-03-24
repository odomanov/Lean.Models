import Relations.StringType

open StringType

abbrev S5 := Str 5
example : S5 := STmin.mk { val := "щпщпа" }
abbrev S0!100 := Str 0 100
abbrev S5!100 := Str 5 100
example : S5!100 := STminmax.mk (ST0.mk "лорпрорвпл" "пггр")


example : Str 5 := str "лорлооо" "лорлао"
example : Str 5 100 := str "лорлооо" "лорлао"

example : S5 := str "лорлооо" "лорлао"
example : S5!100 := str "лорлооо" "лорлао"
