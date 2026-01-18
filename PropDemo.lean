
-- 1. Sort 0 is Prop
-- "Prop" is just a friendly alias for "Sort 0".
#check Prop -- Prop : Type
-- (Lean displays "Type" for Prop's type, but internally it's Sort 1)

-- 2. What lives inside Prop?
-- STATEMENTS live in Prop.
-- Not "True" statements, just ALL statements.

-- Example A: A True Statement
def statement1 : Prop := (1 = 1)

-- Example B: A False Statement
def statement2 : Prop := (2 + 2 = 5)

-- Example C: A Complex Statement
def statement3 : Prop := ∀ x : Nat, x > 0

-- 3. What lives inside those Statements?
-- PROOFS live inside Statements.

-- This is the proof "rfl". It lives inside "statement1".
def proof1 : statement1 := rfl

-- "22" does NOT live in Prop.
-- "22" lives in Nat. Nat lives in Type (Sort 1).
#check 22 -- 22 : Nat

-- "Nat" does NOT live in Prop.
-- "Nat" lives in Type.
#check Nat -- Nat : Type
