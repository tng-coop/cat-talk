/-
  Basic Category Theory in Lean 4
  (Self-contained, no mathlib dependency)
-/

-- 1. Definition of a Category
structure Category (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id  : ∀ (X : Obj), Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  -- Laws
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  assoc   : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
              comp (comp f g) h = comp f (comp g h)

open Category

-- 2. The Universal Property of a Product
--    English (Matching the 'structure' syntax):
--      [Type Name / Question]: `BinaryProduct C A B` (Depends ONLY on A and B).
--      [Meaning   / Answer  ]: This type asserts the EXISTENCE of a structure containing:
--                              1. An object P (The Product Object)
--                              2. Projections π₁, π₂
--                              3. A universal 'lift' capability.
--
--    FOL (The proposition defined by 'BinaryProduct C A B'):
--      Let Prop(A, B) = ∃ P, ∃ π₁: P → A, ∃ π₂: P → B, ... (Laws)
--
--    TEXTBOOK NOTATION:
--      Standard texts usually define "The Product" via the isomorphism of Hom-sets:
--      Hom(X, P) ≅ Hom(X, A) × Hom(X, B)
--      Our `BinaryProduct` structure is the explicit construction of this isomorphism.
--
--    STYLE NOTE (Predicate vs Structure):
--      Standard Math often phrasing: "An object P is a product if..." (Predicate Style).
--      This Lean Code phrasing:      "A Product Structure contains an object P..." (Sigma/Structure Style).
--      We use this style so that the structure *carries* the object P as data we can use.
--
--    NOTE: This structure is a DEFINITION of the concept, not a proof.
--          The type `BinaryProduct C A B` represents the Proposition "A and B have a product".
--          It is not "always true"; it is true (inhabited) only if the category C actually HAS products.
--
--    NOTE ON UNIQUENESS:
--          If such a P exists, it is "unique up to unique isomorphism".
--          Any other object P' with its own projections that satisfies this property
--          will be practically indistinguishable from P (isomorphic).
--
--    MATHEMATICAL PRECISION (Type Theory):
--          Strictly speaking, `BinaryProduct` is a **Type Constructor**.
--          It is a function: `Obj → Obj → Type`.
--          The Type it returns is a **Dependent Sum** (Sigma Type), roughly:
--            Σ (P : Obj), Σ (π₁ : P → A), Σ (π₂ : P → B), ... (Laws)
--          Because of Propositions-as-Types, this Type *represents* the existential proposition.
--
--    We use simple explicit function application instead of custom notation to avoid ambiguity.
structure BinaryProduct {Obj : Type u} (C : Category Obj) (A B : Obj) where
  P : Obj
  π₁ : Hom C P A
  π₂ : Hom C P B
  lift : ∀ {X : Obj}, (Hom C X A) → (Hom C X B) → (Hom C X P)
  -- Laws
  fac₁ : ∀ {X : Obj} (f₁ : Hom C X A) (f₂ : Hom C X B), comp C (lift f₁ f₂) π₁ = f₁
  fac₂ : ∀ {X : Obj} (f₁ : Hom C X A) (f₂ : Hom C X B), comp C (lift f₁ f₂) π₂ = f₂
  uniq : ∀ {X : Obj} (f₁ : Hom C X A) (f₂ : Hom C X B) (g : Hom C X P),
           (comp C g π₁ = f₁) → (comp C g π₂ = f₂) → g = lift f₁ f₂

-- 3. An Example: Concrete implementation for Type (Sets)
def typeCategory : Category Type := {
  Hom     := fun A B => A → B
  id      := fun X x => x
  comp    := fun f g x => g (f x) -- Standard function composition (g ∘ f)
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc   := by intros; rfl
}

-- 4. Verification: The Product of Types is the Product Type (A × B)
def typeProduct (A B : Type) : BinaryProduct typeCategory A B := {
  P := A × B
  π₁ := Prod.fst
  π₂ := Prod.snd
  lift := fun f g x => (f x, g x)
  -- Proofs
  fac₁ := by
    intros X f1 f2
    -- In Types, function equality requires logical extensionality if definitional equality isn't immediately obvious
    funext x
    rfl
  fac₂ := by
    intros X f1 f2
    funext x
    rfl
  uniq := by
    intros X f1 f2 g h1 h2
    funext x
    apply Prod.ext
    -- Use congrFun to apply function equality to an argument
    · exact congrFun h1 x
    · exact congrFun h2 x
}

--------------------------------------------------------------------------------
-- 5. Alternative Definition: Predicate Style (Standard Math)
--------------------------------------------------------------------------------
-- In standard math, we often don't bundle P. We ask "Is THIS P a product?"
-- This is a Prop-valued function (Predicate), not a Type-valued function (Structure).

def is_product_predicate {Obj : Type u} (C : Category Obj) (A B P : Obj)
  (π₁ : Hom C P A) (π₂ : Hom C P B) : Prop :=
    ∀ (X : Obj) (f₁ : Hom C X A) (f₂ : Hom C X B),
      ∃ (u : Hom C X P),
        (comp C u π₁ = f₁) ∧ (comp C u π₂ = f₂) ∧
        (∀ (v : Hom C X P), (comp C v π₁ = f₁) → (comp C v π₂ = f₂) → v = u)

-- Comparison:
-- Structure Style: "Find me a product." -> Returns P
-- Predicate Style: "Check if P is a product." -> Returns True/False
