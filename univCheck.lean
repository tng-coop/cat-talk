
-- 1. Simple Function (Nat -> Nat)
-- Nat : Type 0
-- Result Should be Type 0
#check Nat → Nat

-- 2. "Big" Function (Type -> Type)
-- Type : Type 1
-- Result Should be Type 1
#check Type → Type

-- 3. Mixed Function (Nat -> Type)
-- Nat : Type 0, Type : Type 1
-- Result Should be Type 1 (max 0 1)
#check Nat → Type

-- 4. Set (Nat -> Prop)
-- Nat : Type 0, Prop : Type 0 (Sort 0)
-- Result Should be Type 0
#check Set Nat

-- 5. Prop Function (Nat -> Prop)
#check Nat → Prop
