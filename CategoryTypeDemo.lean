
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic

open CategoryTheory

-- 1. "Category Type" is shorthand.
-- Just like `List Nat` is concrete, `Category Type` usually means `Category Type 0`.
#check Category Type -- Category (Type 0)

-- 2. But we can be explicit!
-- We can make a Category out of ANY universe level.
universe u
variable (MyUniverse : Type (u+1)) -- A placeholder for "The Set of All Types"

-- This is the full polymorphic version:
#check Category.{u} (Type u)

-- 3. Proof that `Type` really means `Type u`
-- When we write this instance, we are defining it for ALL universe levels at once.
instance : LargeCategory (Type u) where
  -- Objects are types in universe `u`
  -- Morphisms are functions between them
  Hom (a : Type u) (b : Type u) := a → b
  id (a : Type u) := fun x => x
  comp f g := g ∘ f

-- 4. Why you don't see `u` often
-- Lean hides universe levels by default to keep you sane.
-- You can see them if you turn on `pp.universes`.
set_option pp.universes true
#check Category Type
-- Result: Category.{0, 1} Type.{0}
