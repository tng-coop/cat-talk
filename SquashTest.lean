
-- 1. Predicate Type (Int -> Prop)
-- This is a "Bag of Functions". It is Data.
-- It lives in `Type` (Sort 1).
-- It is NOT squashed.
#check Int → Prop -- Type

-- 2. Universal Proposition (forall x, P x)
-- This is a "Single Statement". It is Logic.
-- It lives in `Prop` (Sort 0).
-- It IS squashed. (Even though Int is in Type 0, the result is in Prop).
#check ∀ x : Int, x = x -- Prop

-- 3. Arrow Type in Quiver (Hom a b)
-- If v=0, Hom a b : Sort 0 (Prop).
-- This means the "Type of arrows" is a Prop.
-- So there is either 0 arrows (False) or 1 arrow (True).
-- This is squashed.
universe v
variable (A : Type)
variable (MyHom : A → A → Sort 0) -- v=0
#check MyHom -- A → A → Prop
#check MyHom A A -- Prop

-- 4. Arrow Type in Category (Type v)
-- If v=1, Hom a b : Sort 1 (Type).
-- This means "Type of arrows" is a Set.
-- can have 0, 1, or 500 arrows.
