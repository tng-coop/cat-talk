
-- "Free Hand": This function accepts ANY type α.
-- It requires NOTHING from α. It cannot doing anything with x except return it.
def explicitFreeHand (α : Type) (x : α) : α := x

-- "Half Moving" (Constrained):
-- This function accepts ANY type α...
-- BUT it demands that α comes with a "Backpack" containing an LT instance.
def halfMoving (α : Type) [LT α] (x y : α) : Prop :=
  -- Because of the [LT α] constraint, we are allowed to use `<`
  x < y

-- Example: Int carries the backpack.
#check halfMoving Int 1 2

-- Example: RockPaperScissors demands we BUILD the backpack first.
inductive RPS | rock | paper
-- #check halfMoving RPS RPS.rock RPS.paper -- FAILS! No instance.

instance : LT RPS where lt a b := True -- We build the backpack.
#check halfMoving RPS RPS.rock RPS.paper -- NOW it works.
