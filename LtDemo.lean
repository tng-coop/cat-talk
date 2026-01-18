
-- How do you "make" 4 < 5?
-- There are two steps to "making" it.

-- STEP 1: Making the Proposition (The Question)
-- "4 < 5" is a TYPE (a Proposition). It exists because Nat has an instance of LT.
#check 4 < 5  -- Output: 4 < 5 : Prop

-- STEP 2: Making the Proof (The Answer)
-- To "have" 4 < 5, you need to construct a term of that type.
-- For Natural numbers, `a < b` is defined as `(a + 1) ≤ b`.
-- So `4 < 5` really means `5 ≤ 5`.

-- Here is the manual proof term:
example : 4 < 5 :=
  -- In Nat, "4 < 5" is definitionally equal to "5 ≤ 5"
  -- The proof of "5 ≤ 5" is just "reflexivity" (it equals itself).
  Nat.le.refl

-- If you wanted "4 < 6":
example : 4 < 6 :=
  -- This is "5 ≤ 6"
  -- The proof is "Step(Refl)", i.e., "6 is one step after 5, which is ≤ 5"
  Nat.le.step Nat.le.refl
