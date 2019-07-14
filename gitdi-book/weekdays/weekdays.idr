module Weekdays

data Weekday = Mon | Tue | Wed | Thu | Fri | Sat | Sun

total next_day : Weekday -> Weekday
next_day Mon = Tue
next_day Tue = Wed
next_day Wed = Thu
next_day Thu = Fri
next_day Fri = Sat
next_day Sat = Sun
next_day Sun = Mon

first_proof : next_day Mon = Tue
first_proof = Refl

total prev_day : Weekday -> Weekday
prev_day Mon = Sun
prev_day Tue = Mon
prev_day Wed = Tue
prev_day Thu = Wed
prev_day Fri = Thu
prev_day Sat = Fri
prev_day Sun = Sat

second_proof : prev_day Mon = Sun
second_proof = Refl

is_it_monday : Weekday -> Bool
is_it_monday Mon = True
is_it_monday _   = False

-- rewriting day = Mon in is_it_monday day
third_proof : (day : Weekday) -> day = Mon -> is_it_monday day = True
third_proof day day_eq_mon = rewrite day_eq_mon in Refl

is_it_sunday : Weekday -> Bool
is_it_sunday Sun = True
is_it_sunday _   = False

-- for x in weekdays, x = Sun -> is_it_sunday x = true
fourth_proof : (day: Weekday) -> day = Sun -> is_it_sunday day = True
fourth_proof day day_eq_sun = rewrite day_eq_sun in Refl

-- same as Void idris type
data Void'

contradiction_proof : is_it_monday Tue = True -> Void'
contradiction_proof Refl impossible

one_eq_two_contradiction : 1 = 2 -> Void'
one_eq_two_contradiction Refl impossible
