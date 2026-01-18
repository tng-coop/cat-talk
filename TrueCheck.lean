
-- 1. What is True?
-- True is a Proposition (a statement that is always provable).
#check True -- True : Prop

-- 2. What is inside True?
-- The proof named `trivial`.
#check True.intro -- True.intro : True
#check trivial    -- trivial : True

-- 3. Is True a "Type"?
-- In Lean, "Type" usually means Sort 1.
-- True lives in Sort 0 (Prop).
-- So technically: True is a Prop, NOT a Type (uppercase T).
-- But loosely: True is "a type of thing" (lowercase t).
