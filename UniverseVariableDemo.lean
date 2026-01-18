
-- 1. Declaration (No numbers yet!)
-- "universe u" is like declaring a variable argument.
-- It says: "This code works for ANY level u."
universe u

structure MyBox (item : Type u) where
  val : item

-- At this point, `u` is just a placeholder.
-- It's exactly like `def add (x : Int) ...`. `x` has no value yet.

-- 2. Usage (Assignment happens here!)

-- Case A: u = 0
-- We put `Nat` (which is Type 0) into the box.
-- Lean infers: u must be 0.
def box0 : MyBox Nat := { val := 22 }
#check box0 -- MyBox.{0} Nat

-- Case B: u = 1
-- We put `Type` (which is Type 1) into the box.
-- Lean infers: u must be 1.
def box1 : MyBox Type := { val := Nat }
#check box1 -- MyBox.{1} Type

-- Case C: Explicit Assignment
-- We can force u to be a specific number if we want.
#check MyBox.{3} -- A box waiting for a Type 3 item.
