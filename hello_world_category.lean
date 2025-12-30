/-
  The "Hello World" Category
  Demonstrating that Hom can be ANYTHING (even a String!)
-/

import Lean

-- We reuse our basic definition
structure Category (Obj : Type u) where
  Hom : Obj → Obj → Type v
  id  : ∀ (X : Obj), Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  -- (Laws omitted for this toy example to compile easily)

-- 1. Define the Objects (Let's just use Unit, so there is only one object)
abbrev SingleObject := Unit

-- 2. Define the "Hello World" Category
def helloCategory : Category SingleObject := {
  -- IMPLEMENTATION CHOICE:
  -- Instead of functions (A -> B), our arrows are just STRINGS.
  Hom     := fun _ _ => String

  -- The identity arrow is the string "me"
  id      := fun _ => "me"

  -- Composition is String Concatenation!
  -- f ≫ g becomes "f then g"
  comp    := fun f g => f ++ " then " ++ g
}

-- 3. Test it!
def f : helloCategory.Hom () () := "Hello"
def g : helloCategory.Hom () () := "World"

-- Let's compose them:
def h := helloCategory.comp f g

-- The result 'h' is the string: "Hello then World"
#eval h
