/-
  ==============================================================================
  PRACTICE SESSION: Category Theory in Lean 4
  ==============================================================================

  Your Goal: Re-build the structures and instances from memory.

  Tips:
  1. Don't worry about exact names (e.g. `fac1` vs `factor1`), just get the logic.
  2. Use `_` if you want Lean to infer types, but try to be explicit for practice.
  3. If you get stuck on syntax, peek at `basic_cat.lean`, then close it and type it yourself.
-/

-- STEP 1: Define the `Category` Structure
-- Input: An Object Type `Obj`.
-- Fields needed:
--   1. `Hom` : The type of arrows between X and Y.
--   2. `id`  : The identity arrow for every X.
--   3. `comp`: The composition of two arrows (f then g).
--   4. Laws  : Left Identity, Right Identity, Associativity.
-- -----------------------------------------------------------------------------
structure Abc (i:Integer)
structure Category (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id  : ∀ {X : Obj}, Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp id  f = f
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f id = f
  assoc   : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
              comp (comp f g) h = comp f (comp g h)



open Category


-- STEP 2: Define the `BinaryProduct` Structure
-- Input: A Category `C` and two objects `A` and `B`.
-- Fields needed:
--   1. `P`    : The definition of the product object itself.
--   2. `π₁`   : Projection to A.
--   3. `π₂`   : Projection to B.
--   4. `lift` : The universal function (constructs the arrow to P).
--   5. Laws   : Factorization 1, Factorization 2, Uniqueness.
-- -----------------------------------------------------------------------------
structure BinaryProduct {Obj : Type u} (C : Category Obj) (A B : Obj) where
  P : Obj
  π₁ : Hom C P A
  π₂ : Hom C P B
  lift : ∀ {X : Obj}, (Hom C X A) → (Hom C X B) → (Hom C X P)
  fac₁ : ∀ {X : Obj} (f₁ : Hom C X A) (f₂ : Hom C X B), comp C (lift f₁ f₂) π₁ = f₁
  fac₂ : ∀ {X : Obj} (f₁ : Hom C X A) (f₂ : Hom C X B), comp C (lift f₁ f₂) π₂ = f₂
  uniq : ∀ {X : Obj} (f₁ : Hom C X A) (f₂ : Hom C X B) (g : Hom C X P),
           (comp C g π₁ = f₁) → (comp C g π₂ = f₂) → g = lift f₁ f₂






-- STEP 3: Implement the `typeCategory` Instance
-- Define a Category where Objects are `Type` and Morphisms are functions.
-- PRO TIP: You will need tactics for the laws (`intros`, `rfl`, or `funext`).
-- -----------------------------------------------------------------------------
def typeCategory : ...






-- STEP 4: Verification - The Product of Types
-- Prove that the standard `A × B` (Cartesian Product) satisfies your structure.
-- This is where you will use `Prod.ext`, `congrFun`, and `dsimp`.
-- -----------------------------------------------------------------------------
def typeProduct (A B : Type) : ...
