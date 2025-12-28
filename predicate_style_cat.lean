/-
  Predicate Style Category Theory
  (Defining UP without Sigma Types / Structures)
-/

structure Category (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id  : ∀ (X : Obj), Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  -- (laws omitted for brevity)

open Category

--
-- THE PREDICATE DEFINITION (No Sigma, No Structure binding P)
-- "is_product P A B" is a Yes/No question about P.
--
def is_product {Obj : Type u} (C : Category Obj) (A B P : Obj)
  (π₁ : Hom C P A) (π₂ : Hom C P B) : Prop :=
    ∀ (X : Obj) (f₁ : Hom C X A) (f₂ : Hom C X B),
      ∃ (u : Hom C X P),
        (comp C u π₁ = f₁) ∧ (comp C u π₂ = f₂) ∧
        (∀ (v : Hom C X P), (comp C v π₁ = f₁) → (comp C v π₂ = f₂) → v = u)

--
-- USAGE COMPARISON
--

-- 1. Predicate Style (This file):
--    You must ALREADY have a P to ask the question.
--    "Is my_P a product?" -> True/False
--    (You pass P as an ARGUMENT)

-- 2. Structure Style (Your other file):
--    You ask for a product, and it GIVES you a P.
--    "Give me the product." -> returns { P: ..., proof: ... }
--    (You get P as a RESULT)
