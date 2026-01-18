
-- 1. Can x be 22? (NO)
-- Input: x : Type 4
-- Value: 22
-- Result: FAIL.
-- "22" is Data. It lives in `Nat`.
-- "Type 4" is a Universe bucket. It only holds huge Types.
-- def x : Type 4 := 22 -- Error

-- 2. Can x be Nat? (NO - Surprising!)
-- Input: x : Type 4
-- Value: Nat
-- Result: FAIL.
-- `Nat` lives in `Type` (Type 1).
-- `Type 4` expects items of `Type 3`.
-- Lean is strict! You cannot put a small Type 1 item into a huge Type 4 bucket directly.
-- def y : Type 4 := Nat -- Error: Expected Type 4, got Type 1

-- 3. The Strict Ladder
-- You have to climb one rung at a time.
def val0 : Nat := 22          -- 22 Lives in Nat
def val1 : Type := Nat        -- Nat Lives in Type (Type 0)
def val2 : Type 1 := Type     -- Type 0 Lives in Type 1
def val3 : Type 2 := Type 1   -- Type 1 Lives in Type 2
def val4 : Type 3 := Type 2   -- Type 2 Lives in Type 3
def val5 : Type 4 := Type 3   -- Type 3 Lives in Type 4

-- So if `x : Type 4`, x MUST be a `Type 3`.
-- It is a Universe that contains Universes that contains Universes...
