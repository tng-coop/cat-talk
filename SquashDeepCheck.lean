
-- User Hypothesis: Type 4 -> True : Prop ??

-- 1. The Function Type (Arrow)
-- This is the type of functions that accept a Universe and return True.
-- Since this is a FUNCTION space, it usually lives in Type.
#check Type 4 → True
-- Expectation: Type 5 (because destination is Prop, so it might be imax(5, 0) => 5?)
-- Or does it squash?

-- 2. The Proposition (Dependent Arrow / Forall)
-- This is the CLAIM that "For all Type 4s, True holds".
#check ∀ (x : Type 4), True
-- Expectation: Prop (Squashed).

-- 3. A specific function (Instance of 1)
def myFunction : Type 4 → True := fun _ => trivial
#check myFunction -- Type 4 -> True
