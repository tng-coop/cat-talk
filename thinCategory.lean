import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Basic

open CategoryTheory

-- A "Thin Category" is simply a category where there is at most one unique morphism
-- between any two objects.
--
-- In Mathlib, the `Preorder` instance creates a Category.
-- However, strict "Thinness" depends on the universe levels.

universe u

-- 1. Preorders as Categories
-- If X is a Preorder, Mathlib provides a `SmallCategory X`.
-- `SmallCategory` means the arrows live in the SAME universe as the objects.
--
-- If X : Type u, then Hom : X -> X -> Type u.
-- Since the relation `a ≤ b` is a Prop, Mathlib wraps it in a wrapper (ULift/PLift)
-- to make it a Type.

-- 2. Concrete Example: Bool
-- Bool is in Type 0. So its Category will be Category.{0}.
-- This means the arrows are in Type 0 (which contains PLift Prop).

def BoolPoset : Type := Bool

instance : Preorder BoolPoset where
  le a b := (a = true) → (b = true)
  le_refl a := fun h ↦ h
  le_trans a b c hab hbc := fun wa ↦ hbc (hab wa)

-- This instance is automatically found.
def BoolCat : Category.{0} BoolPoset := inferInstance

-- 3. Verifying "Thinness" (Subsingleton Homsets)
-- The morphisms are wrappers around Props.
-- While they behave like Props, they are technically Types.
-- So `rfl` (definitional equality) might not always work directly if the wrapper
-- hides implementation details, but they are provably equal because they are Subsingletons.

variable (A B : BoolPoset)
variable (f g : A ⟶ B)

-- We can prove they are equal because the Hom-set is a Subsingleton.
example : f = g := Subsingleton.elim f g
