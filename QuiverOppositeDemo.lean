import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Opposites -- This is the crucial missing import for category instances!

open CategoryTheory
open Opposite

-- 1. Setup a basic Quiver (Directed Graph)
variable (V : Type) [Quiver V]

-- 2. "Opposite" is just a type wrapper
-- If `a : V`, then `op a` is the same point in the "Opposite" universe.
variable (a b : V)

#check op a
-- op a : Vᵒᵖ

#check unop (op a)
-- unop (op a) : V (We get back to the original type)


-- 3. The Arrows are Reversed
-- If we have an arrow `f : a ⟶ b`,
-- The opposite arrow lives in `Vᵒᵖ` and goes `op b ⟶ op a`.

variable (f : a ⟶ b)

-- The `op` function works on arrows too!
#check f.op
-- f.op : op b ⟶ op a   (Notice the direction flip!)

-- Explicit type assertion to prove it:
#check (f.op : op b ⟶ op a)


-- And we can go back
#check f.op.unop
-- f.op.unop : a ⟶ b


-- 4. In a real Category
variable {C : Type} [Category C]
variable {x y z : C}
variable (f' : x ⟶ y) (g' : y ⟶ z)

-- Composition in opposite is reversed
-- In C:   f' ≫ g'  (f then g)
-- In Cᵒᵖ: g'.op ≫ f'.op
#check g'.op ≫ f'.op
-- g'.op ≫ f'.op : op z ⟶ op x
