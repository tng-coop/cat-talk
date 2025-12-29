import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.List.Basic

/-
  ==============================================================================
  Category Theory in Lean 4 (Using Mathlib)
  ==============================================================================

  We have now switched from our manual educational implementation to the
  official Mathlib library.
-/

open CategoryTheory
open MonoidalCategory

-- 1. Standard Category
--    Category is now a Type Class defined in Mathlib.
example : Category Type := inferInstance

-- 2. Monoidal Category
--    MonoidalCategory is also fully defined, with all Pentagon/Triangle identities verified.
example : MonoidalCategory Type := inferInstance

-- 3. Working with Coherence (Mac Lane's Theorem)
--    Mathlib provides the `coherence` tactic (imported above) to automatically
--    solve equations that hold by Mac Lane's Coherence Theorem.

--    This theorem states that any diagram built from associators and unitors commutes.

-- Example: The Pentagon Identity
-- This is one of the axioms of a Monoidal Category, but 'coherence' can prove it
-- (and much more complex diagrams) automatically.
example {C : Type u} [Category C] [MonoidalCategory C] (W X Y Z : C) :
  tensorHom (α_ W X Y).hom (𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫ tensorHom (𝟙 W) (α_ X Y Z).hom
  = (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom :=
  by coherence

-- 4. Monads and General Associativity
--    Monads are Monoids in the category of Endofunctors (C ⥤ C).
--    Because (C ⥤ C) is a Strict Monoidal Category, the associativity is definitional
--    and we can use standard Monoid theorems.

--    The "General Associativity Theorem" (guaranteeing T^n -> T is unique)
--    is formally realized in Lean as theorems about List.prod.

section MonadGeneralAssociativity

  variable {M : Type} [Monoid M]

  -- This theorem mimics the core library proof (List.prod_append) to demonstrate
  -- the inductive logic that allows the simple Monad Axiom (3 terms)
  -- to govern arbitrarily complex chains (N terms).

  theorem general_associativity_demo (L1 L2 : List M) : (L1 ++ L2).prod = L1.prod * L2.prod := by
    induction L1 with
    | nil =>
      -- Base Case: [] ++ L2 = L2
      simp
    | cons head tail ih =>
      -- Inductive Step: (h :: t) ++ L2
      -- Use simp to reduce append and rewrite logic in one go
      simp [List.cons_append, List.prod_cons, mul_assoc, ih]

end MonadGeneralAssociativity
