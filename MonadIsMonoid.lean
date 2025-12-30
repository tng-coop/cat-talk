import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monad.EquivMon

/-!
# A Monad is a Monoid in the Category of Endofunctors

This file demonstrates the formal statement "A Monad is a Monoid in the category of Endofunctors"
using the Lean Mathlib library.

We map the components of a `Monad` to the components of a `Mon_` (Monoid Object).
-/

namespace MonadIsMonoidDemo

open CategoryTheory MonoidalCategory

-- Let C be any Category (Type u)
variable (C : Type*) [Category C]

/-
## 1. The Environment: The Category of Endofunctors

The statement requires a Monoidal Category.
The category of endofunctors `C ⥤ C` forms a strict monoidal category where:
*   **Objects**: Functors `F : C ⥤ C`
*   **Tensor Product (⊗)**: Functor Composition (`⋙`)
*   **Tensor Unit (𝟙_)**: Identity Functor (`𝟭 C`)

-/
-- The category of endofunctors `C ⥤ C` forms a strict monoidal category.
-- In Mathlib, this instance is not global by default, so we enable it locally.
attribute [local instance] endofunctorMonoidalCategory

#synth MonoidalCategory (C ⥤ C)

/-
## 2. The Correspondence

We define a helper function to show exactly how a `Monad` structure fits into a `Mon` (Monoid Object) structure.
-/

/-- Constructing a Monoid Object from a Monad -/
def monadToMonoid (T : Monad C) : Mon (C ⥤ C) where
  -- 1. The Underlying Object (The Functor)
  X := T.toFunctor

  -- 2. The Monoid Structure
  -- We provide the MonObj instance, mapping η to one and μ to mul.
  mon := {
    one := T.η
    mul := T.μ
    one_mul := by ext; simp
    mul_one := by ext; simp
    mul_assoc := by ext; simp [T.assoc]
  }

/-
## 3. The Equivalence

Mathlib provides the formal proof that the category of Monads on C is equivalent
to the category of Monoid objects in (C ⥤ C).
-/

noncomputable def equivalence : Monad C ≌ Mon (C ⥤ C) :=
  CategoryTheory.Monad.monadMonEquiv C

/-
## 4. Verification

We can verify the types align perfectly.
-/

variable (T : Monad C)

-- The type of η matches the type of `one` in the Monoidal category of endofunctors
example : (𝟭 C ⟶ T.toFunctor) = (𝟙_ (C ⥤ C) ⟶ T.toFunctor) := rfl

-- The type of μ matches the type of `mul`
-- Note: T ⊗ T in the category of endofunctors IS DEFINED as composition T ⋙ T.
example : (T.toFunctor ⋙ T.toFunctor ⟶ T.toFunctor) = (T.toFunctor ⊗ T.toFunctor ⟶ T.toFunctor) := rfl

end MonadIsMonoidDemo
