
import Mathlib.Order.Defs.PartialOrder

-- 1. "LE" is just a relationship shape.
-- We can define it to mean ANYTHING we want.
-- Here, I define "Less-Equal" to actually mean "Is strictly Greater Than" (Crazy!)
instance : LE Nat where
  le a b := a > b

-- The system accepts this! Syntax doesn't care about meaning.
-- Now I can write "2 ≤ 1" and it evaluates to True because I said LE means >.
example : 2 ≤ 1 := by
  -- This is true because my definition of ≤ is actually >
  show 2 > 1
  simp

-- 2. SO HOW DOES IT HOLD WATER?
-- The "Meaning" comes when you try to become a "Preorder".
-- A Preorder REQUIRES that `≤` be Reflexive (a ≤ a).

-- This will FAIL to compile because my crazy definition (>) represents
-- a relationship where `a > a` is impossible.
def crazyPreorder : Preorder Nat := {
  le := (· > ·) -- Use my crazy definition
  lt := (· > ·)
  -- The system demands proof that `le` is reflexive.
  le_refl := by
    intro a
    -- Goal: a ≤ a
    -- Definition: a > a
    -- ERROR: Impossible to prove!
    sorry
  le_trans := sorry
  lt_iff_le_not_ge := sorry
}
