-- Type T = Nat (conceptually)

-- 1. Allowed: T -> T
-- This is standard recursion.
-- "To make a T, give me a T (and I will wrap it)".
inductive Good
  | mk : Good → Good

-- 2. Question: (T -> T) -> T
-- This means: "To make a T, give me a FUNCTION that transforms T to T".
-- This puts T in a "Negative Position" (Left side of arrow).
-- It allows logical paradoxes if permitted.

-- 3. Allowed: T -> T -> T (Right Associative)
-- This means `T -> (T -> T)`.
-- Both `T`s are just inputs.
-- This is a Binary Tree node!
inductive MyBinTree
  | mk : MyBinTree → MyBinTree → MyBinTree

-- 4. BANNED: (T -> T) -> T (Left Associative grouping)
-- This means the input IS A FUNCTION that takes T.
inductive Bad
  | mk : (Bad → Bad) → Bad

-- THE "SIZE" EXPLANATION (Cantor's Theorem):
-- Why is `T -> T` allowed, but `(T -> Bool) -> T` banned?
-- It's about SIZE.

-- 1. `mk : T -> T`
--    To build a T, you pack ONE existing T.
--    This is fine. Infinities can hold themselves + 1.

-- 2. `mk : (T -> Bool) -> T`
--    To build a T, you pack a FUNCTION defined on ALL Ts.
--    How many such functions are there? `2 ^ |T|`.
--    Cantor's Theorem proves: `2 ^ |T| > |T|`.
--    It is strictly BIGGER.
--    You cannot fit the Power Set of T inside T.
--    That's why Lean forbids it. It's mathematically impossible.

-- UNCOMMENTING THE ABOVE GIVES:
-- "arg #1 of 'Bad.mk' has a non-positive occurrence of the datatypes being declared"
