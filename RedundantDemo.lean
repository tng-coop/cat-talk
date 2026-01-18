
-- 1. A new Type (MyInt)
structure MyInt where val : Int

-- 2. A Function (The Logic)
-- This corresponds to `Int.lt`. It exists, it works.
def MyInt.lt (a b : MyInt) : Prop := a.val < b.val

-- BUT... we cannot use the syntax yet.
-- #check (MyInt.mk 1) < (MyInt.mk 2)
-- ERROR: failed to synthesize instance LT MyInt

-- 3. The "Redundant" Instance (The Bridge)
-- This looks trivial: "lt := lt".
-- But it is the critical wiring that connects the Syntax (<) to the Logic (MyInt.lt).
instance : LT MyInt where
  lt := MyInt.lt

-- 4. NOW it works
#check (MyInt.mk 1) < (MyInt.mk 2)
