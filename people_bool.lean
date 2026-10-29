-- EXPLAINING WITH ONLY PEOPLE AND BOOL

-- 1. THE PEOPLE (X)
-- Let's say we have a tiny village with just 2 people.
inductive Person
| Alice
| Bob
deriving Fintype, Repr, DecidableEq

open Person

-- 2. THE PATTERNS (X -> Y)
-- A "Pattern" (Function) is just a pair of Bools: (Answer for Alice, Answer for Bob)

-- Pattern 1: (False, False) - Shaves nobody.
def p1 : Person → Bool := fun _ => false

-- Pattern 2: (False, True) - Shaves only Bob.
def p2 : Person → Bool
| Alice => false
| Bob   => true

-- Pattern 3: (True, False) - Shaves only Alice.
def p3 : Person → Bool
| Alice => true
| Bob   => false

-- Pattern 4: (True, True) - Shaves everyone.
def p4 : Person → Bool := fun _ => true

-- 3. THE MISMATCH
-- We have 2 People: {Alice, Bob}
-- We have 4 Patterns: {p1, p2, p3, p4}

-- PROBLEM: 4 > 2.
-- You CANNOT treat "The Set of Patterns" as "The Set of People".
-- If you try to say "Every Person is a Pattern", you run out of People.
-- You will have 2 Leftover Patterns that no person represents.

-- 4. THE BARBER PARADOX
-- The Barber Paradox is just a fancy way of pointing at one of the Leftover Patterns.
-- It constructs a pattern that is GUARANTEED to be leftover.
-- "Take Alice's self-value and flip it. Take Bob's self-value and flip it."
-- This creates a pattern that is neither Alice's pattern nor Bob's pattern.
