
-- Testing Universe Cumulativity
-- User Question: Can Type 0 : Type 4?

-- 1. Direct Assignment
-- Type 0 (aka Type) has type Type 1.
-- Does it also have type Type 4?
def test1 : Type 4 := Type 0

-- 2. What about Nat?
-- Nat : Type 0.
-- Does Nat : Type 4?
def test2 : Type 4 := Nat

-- 3. What about generic U?
universe u
def test3 : Type (u+2) := Type u
