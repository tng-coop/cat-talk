import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.List.Basic
import Mathlib.CategoryTheory.Opposites -- Required for unop

open CategoryTheory
open Opposite -- For unop

/-!
# Category Theory in Lean 4: The "Zero to Hero" Guide
This file explains the *Language* of Lean before the *Math* of Categories.

---

# Part 1: The Atoms (Super Basics)

Before we talk about "Categories", we must understand the atoms of the universe.

## 1.1 Terms and Types
Everything in Lean is a **Term** (data) which has a **Type**.
Syntax: `t : T` means "t is a term of type T".
-/

-- `5` is a term. `Nat` is its type.
#check 5

-- `Nat` is a term. `Type` is its type.
#check Nat

/-!
## 1.2 Universes (`Sort` and `Type`)
What is the type of `Type`? It is `Type 1`.
Types are organized in an infinite hierarchy of **Universes** to avoid paradoxes (Russell's Paradox).

*   `Type 0` (or just `Type`): The universe of "normal" types (Nat, Bool, List Nat).
*   `Type 1`: The universe containing `Type 0`.
*   `Type u`: A polymorphic universe variable `u`.

**Syntax Decoder**: `.{u}`
When you see `LargeCategory.{0} Type`, the `.{0}` is passing `0` as the universe argument `u`.
-/

-- The type of `Type` is `Type 1`.
#check Type

/-!
## 1.3 Functions (`→` vs `⟶`)
*   **`→` (Right Arrow)**: The built-in Logical Implication / Function Arrow.
    `A → B` is the type of functions from A to B.
    Constructed using Lambda syntax: `fun x => ...`
*   **`⟶` (Long Right Arrow)**: The **Category Theory Morphism**.
    This is notation for `Quiver.Hom X Y`.
    It *might* be a function (in `Category Type`), but it might be a matrix, a path, or a proof.
-/

-- A built-in function
#check fun (x : Nat) => x + 1

/-!
---

# Part 2: The Containers

Lean has two main ways to package data: `structure` and `class`.

## 2.1 Structures (Data)
A `structure` is a "Product Type". It bundles data fields together.
We use it for things that are **Unique Data Schemas**, like a `Cone` or a `complex number`.

Syntax: `structure Name where ...`
Constructor: `⟨x, y⟩` (Anonymous Constructor)

## 2.2 Classes (Interfaces)
A `class` is exactly a `structure`, but it is registered with the **Type Class Synthesis** system.
We use it for **Behaviors** or **Properties** attached to a type, like `Category`, `Monoid`, or `Inhabited`.

Syntax: `class Name ...`
Usage: `[C : Category X]` tells Lean "Find me a Category instance for X automatically".

---

# Part 3: The Grammar (Brackets)

The shape of the brackets tells Lean **How to find the argument**.

## 3.1 Explicit Arguments `(...)`
*   `(x : Nat)`: You **must** provide this argument manually.
*   Example: `(p : X = Y)` in `eqToHom`.

## 3.2 Implicit Arguments `{...}`
*   `{x : Nat}`: Lean **infers** this from context.
*   Example: In `id : X → X`, if I write `id 5`, Lean infers `{X}` must be `Nat`.

## 3.3 Instance Arguments `[...]`
*   `[Category C]`: Lean asks the **Synthesizer** to find a declared instance.
*   It searches its database of `instance` definitions.

---

# Part 4: Category Theory (The Application)

Now we apply the Atoms and Grammar to build Category Theory.

## 4.1 The Definition
The definition of `Category` uses all the concepts above:
1.  It is a `class` (Interface).
2.  It uses Universes `.{v}` for morphisms.
3.  It extends `Quiver` (which defines the `⟶` arrow).
-/

-- Kernel Inspection: Explicit Universe Instantiation
-- We force the morphism universe to be `0`.
#check LargeCategory.{0} Type

/-!
## 4.2 The Elaborator & Unifier
When we write `Category Type`, Lean's **Elaborator** calls the **Unifier**.
The Unifier checks transparency settings:
1.  **Reducible** (`abbrev`): Always unfold.
2.  **Semireducible** (`def`): Unfold if stuck.
3.  **Irreducible** (`opaque`): Never unfold.
-/

#synth LargeCategory Type

/-!
# 5. Path Induction: Logic (`=`) to Geometry (`⟶`)

How do we turn an equality `p : X = Y` into a morphism `X ⟶ Y`?
We use the Inductive nature of `Eq`.

**Syntax Decoder**: `match p with | rfl => ...`
This is **Dependent Pattern Matching**.
Because `Eq` has only one constructor `refl`, if we match `rfl`, Lean *replaces* `Y` with `X` everywhere.
-/

-- Syntax: `{X Y}` are implicit. `(p)` is explicit.
def myEqToHom {X Y : Type} (p : X = Y) : X ⟶ Y :=
  match p with
  | rfl => 𝟙 X

/-!
# 6. Yoneda: Continuation Passing Style

**Syntax Decoder**: `(Type)ᵒᵖ` and `.unop`
*   `(Type)ᵒᵖ`: Semantic sugar for `Opposite Type`.
*   `f.unop`: Semantic sugar for `Opposite.unop f`.
-/

def YonedaEmbedding (X : Type) : (Type)ᵒᵖ ⥤ Type where
  obj Y := (unop Y) ⟶ X
  map f := fun (g : (unop _) ⟶ X) => f.unop ≫ g
  map_id := by
    intros; dsimp [CategoryStruct.id]; funext; simp
  map_comp := by
    intros; dsimp [CategoryStruct.comp]; funext; simp

/-!
# 7. Adjunctions: Foreign Function Interfaces

We implement Currying: `(A × B ⟶ C) ≅ (A ⟶ (B ⟶ C))`.
This "Foreign Function Interface" translates problems from "Product World" to "Function World".
-/

def curryingAdjunction {A B C : Type} : (A × B ⟶ C) ≅ (A ⟶ (B ⟶ C)) where
  hom f := fun a b => f (a, b)
  inv g := fun p => g p.1 p.2
  hom_inv_id := by
    funext f; funext p; cases p; rfl
  inv_hom_id := by
    funext g; funext a; funext b; rfl

/-!
# 8. Limits: Data Structures
A Limit is a **Container** (Structure) that is the "Best" (Terminal).

**Syntax Decoder**: `⟨...⟩` (Anonymous Constructor)
In the proof below, `refine ⟨...⟩` builds the `ExistsUnique` structure on the fly.
-/

structure MyCone (X Y : Type) where
  pt : Type
  π₁ : pt ⟶ X
  π₂ : pt ⟶ Y

def productCone (X Y : Type) : MyCone X Y where
  pt := X × Y
  π₁ := Prod.fst
  π₂ := Prod.snd

-- Universal Property Proof
example {Z A B : Type} (f : Z ⟶ A) (g : Z ⟶ B) :
  ∃! (u : Z ⟶ A × B), (u ≫ Prod.fst = f) ∧ (u ≫ Prod.snd = g) := by
  -- SYNTAX: `?_` creates a "Hole" (Goal).
  refine ⟨fun z => (f z, g z), ⟨?_, ?_⟩, ?_⟩
  -- SYNTAX: `·` (Bullet) focuses on the goal.
  · dsimp [CategoryStruct.comp]; rfl
  · dsimp [CategoryStruct.comp]; rfl
  · intro v h
    funext z
    apply Prod.ext
    · have h1 := h.1; exact congrFun h1 z
    · have h2 := h.2; exact congrFun h2 z

/-!
# 9. Conclusion

We have rebuilt Category Theory from the particles up:
1.  **Atoms**: Types, Terms, Universes.
2.  **Containers**: Structures and Classes.
3.  **Grammar**: Arguments (`{}`, `()`, `[]`) and Arrows (`→`, `⟶`).
4.  **Applications**: Using these to build Products, Adjunctions, and Embeddings.

You now possess the "Source Code" logic of the Lean Kernel.
-/
