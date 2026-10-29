-- WHAT IS TRUE?
-- It is a Type (a Proposition) with EXACTLY ONE value.

-- 1. The Definition of True
-- It is defined exactly like this:
-- inductive True : Prop where
--   | intro : True

#print True
-- inductive True : Prop
-- constructors:
-- True.intro : True

-- 2. The Definition of "trivial"
-- "trivial" is just the name for that one value.
def my_trivial : True := True.intro
#check trivial -- True

-- 3. COMPARISON: True vs 1=1
-- 1=1 is ALSO a proposition with exactly one value (rfl).
#check 1=1 -- Prop
example : 1=1 := rfl

-- "True" is the "Generic Empty Box with One Ball".
-- "1=1" is a "Specific Box with One Ball" (where the ball is the path from 1 to 1).

-- 4. COMPARISON: False vs 1=2
-- False is a proposition with ZERO values.
-- inductive False : Prop where (no constructors)

-- 1=2 is a proposition with ZERO values (no path from 1 to 2).
-- They are both "Empty Boxes".

-- 5. Why do we need "True"?
-- Sometimes you need a "No-Op" proposition.
-- "If X then True" (Always provable, carries no info).
