
import Mathlib.Data.Int.Order.Basic

-- 1. "INT" HAS TWO HOMES

-- HOME A: SYNTAX (Init.Data.Int.Basic)
-- Core Lean defines the "Shape" (LE/LT) immediately so you can write code.
-- It defines `Int.le` as a semantic function:
#check Int.le -- Int → Int → Prop (NonNeg (b - a))

-- And it registers the "Empty Syntax Suit" instance:
-- instance : LE Int where le := Int.le

-- HOME B: MEANING (Mathlib.Data.Int.Order.Basic)
-- Mathlib (and Std) provides the "Brain" (LinearOrder).
-- This is where the syntax gets its degree.

-- Here is what `LinearOrder Int` actually looks like under the hood:
-- We construct an example to prove we can perform the "marriage" manually.
example : LinearOrder Int := {
  -- The Syntax (reusing what Core Lean gave us)
  le := Int.le
  lt := Int.lt

  -- The Proofs (The "Water")
  le_refl := Int.le_refl         -- Proof that a ≤ a
  le_trans := @Int.le_trans      -- Proof of transitivity (Needs @ for implicits)
  le_antisymm := @Int.le_antisymm -- Proof that a≤b ∧ b≤a → a=b
  le_total := Int.le_total       -- Proof that a≤b ∨ b≤a (Linear!)

  -- The Connection between < and ≤
  -- Int defines < as (a+1 ≤ b), so we must prove this matches (a≤b ∧ ¬b≤a)
  lt_iff_le_not_ge := @Int.lt_iff_le_not_le

  -- The Decidability (Computer Science)
  -- This allows `if 4 < 5` to run as code.
  toDecidableEq := Int.instDecidableEq
  toDecidableLE := Int.decLe
  toDecidableLT := Int.decLt
}

-- You can see the official instance name here:
#check Int.instLinearOrder
