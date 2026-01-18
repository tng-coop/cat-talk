
-- 1. Is Prop exactly Sort 0?
-- We prove they are EQUAL (Syntactically identical under the hood).
example : Prop = Sort 0 := rfl

-- 2. Is Type exactly Sort 1?
example : Type = Sort 1 := rfl

-- 3. Is Type u exactly Sort (u+1)?
universe u
example : Type u = Sort (u+1) := rfl

-- 4. What about Sort?
-- Sort is the "Master Universe".
-- Sort 0 (Prop) is the "Bottom" universe for Logic.
-- Sort 1 (Type) is the "First" universe for Data.
