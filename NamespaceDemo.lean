
import Init.Data.Int.Basic

-- 1. Int.lt (The "Manufacturer's Function")
-- Defines definitions specific to Integers.
-- Full Name: Int.lt
-- Definition: (a + 1) ≤ b
#check Int.lt -- Int → Int → Prop


-- 2. LT.lt (The "Universal Interface")
-- Defines the shape of "Less Than" for ANY type.
-- Full Name: LT.lt
-- Definition: Look up the instance and call its 'lt' field.
#check LT.lt -- (α : Type) → [LT α] → α → α → Prop


-- 3. The Connection
-- The instance maps the Interface (LT.lt) to the Implementation (Int.lt).
-- Syntax:
-- instance : LT Int where
--   lt := Int.lt
--   ^^    ^^^^^^
-- Field   Value
