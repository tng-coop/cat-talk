import Mathlib.CategoryTheory.Category.Basic

-- The User's Hypothesis:
-- "If it is class [with defaults/impls], then you do not need to instantiate [for each type]."

-- 1. Defining the Class
class FreePass (α : Type) where
  ticket : String := "Admit One"

-- 2. The "Blanket Instance" (The Global Instantiation)
-- We define an instance for ANY type `α`.
-- Because we have defaults, we don't even need to write a body!
instance : FreePass α where
  -- Empty body! Defaults take over.

-- 3. The Result: Automatic Availability
-- We never explicitly said "Nat has a FreePass".
-- But it works!
example : FreePass Nat := inferInstance

-- We never said "String has a FreePass".
-- But it works!
example : FreePass String := inferInstance

-- We never said "Bool has a FreePass".
example : FreePass Bool := inferInstance

-- PROOF:
-- We can call the function on ANY type immediately.
#eval (inferInstance : FreePass Nat).ticket   -- "Admit One"
#eval (inferInstance : FreePass Bool).ticket  -- "Admit One"

-- CONCLUSION:
-- You are right!
-- If you provide a "Blanket Instance" (instance : Class α),
-- then you DO NOT need to instantiate individual types.
-- They are all covered automatically.
