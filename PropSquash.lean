
-- 1. The "Normal" Rule (The Balloon)
-- If you combine Type u and Type v, you get the MAX.
-- It grows to fit the largest thing.
universe u
def NormalFunction := Type u → Type u
#check NormalFunction
-- Result: Type (u+1)
-- (The function type is bigger than the input)


-- 2. The "Squash" Rule (The Black Hole)
-- If the target is Prop, the Universe level of the input DOES NOT MATTER.
-- It gets "squashed" down to Prop (Sort 0).
def PropFunction := Type u → Prop
#check PropFunction
-- Result: Type!!! (Wait, the type of the FUNCTION is Type u)
-- Let's check the RESULT of the quantification:

variable (P : Type u → Prop)
#check ∀ (x : Type u), P x
-- Result: Prop
-- Even though we are looping over a HUGE Type u, the result is just a tiny Prop.

-- 3. Why is this cool?
-- It allows us to say signatures like:
-- "For ALL types in the universe, Logic applies."
-- Without raising the universe level of Logic itself.
