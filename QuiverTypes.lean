import Mathlib.Combinatorics.Quiver.Basic

universe v u
variable {V : Type u} [Quiver.{v} V]
variable {a b : V}

-- We define a function taking an arrow f
def check_type (f : a ⟶ b) : Unit := ()

-- Let's inspect what f is.
#check @check_type
-- Output: ... (f : a ⟶ b) ...

-- But what is (a ⟶ b)?
-- It is Quiver.Hom a b
#check (a ⟶ b)
-- Output: a ⟶ b : Sort v
