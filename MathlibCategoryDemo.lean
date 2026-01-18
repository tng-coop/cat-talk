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

/-!
## 2.3 Universe Engineering: Type Theory & Cardinality

The definition `class Quiver (V : Type u) where Hom : V → V → Sort v` stratifies the category to ensure logical consistency and precise cardinality control.

### 1. Stratification and Consistency
To avoid foundational inconsistencies like **Girard's Paradox** (the Type Theory equivalent of Russell's Paradox), types must be stratified into a universe hierarchy: `Type u : Type (u+1)`.
*   `u` is the universe level of the **Objects**.
*   `v` is the universe level of the **Morphisms**.

### 2. Cardinality Distinctions
This separation defines the "Size" of the category in terms of relative universe levels:

*   **Small Category** (`u = v`):
    *   Satisfies `Obj : Type u` and `Hom(X, Y) : Type u`.
    *   The category structure itself usually lives in `Type (u+1)`.
    *   Example: A Monoid or a Finite Category.

*   **Large Category** (`u = v + 1`):
    *   `Obj : Type (u+1)` while `Hom(X, Y) : Type u`.
    *   Example: `Category.{0} Type`. The objects are Types (living in `Type 1`), but morphisms are functions (living in `Type 0`).
    *   This corresponds to a **Proper Class** in NBG Set Theory relative to the morphisms.

*   **Locally Small Category**:
    *   Formally defined by the condition that for all `X, Y`, the type `Hom(X, Y)` lives in a universe `v <= u`.
    *   This local smallness is the necessary condition for the **Yoneda Lemma**, ensuring the embedding lands in the category of Sets.

### 3. Propositional Resizing (`Sort 0`)
The use of `Sort v` allows `v=0` (Prop).

*   **Proof Irrelevance**: For any `P : Prop` and `p, q : P`, we have `p ≡ q` (Definitional Equality).
*   **Subsingleton Hom-Sets**: If `Hom(X, Y) : Prop`, then `Hom(X, Y)` has at most 1 element.
*   **Thin Categories**: A category where every Hom-set is a subsingleton is isomorphic to a **Preorder**.
    *   Reflexivity holds by identity.
    *   Transitivity holds by composition.
    *   All diagrams commute by definition (all parallel paths are equal).

### 2.4 The Structure (Directed Multigraphs)

Mathematically, a `Quiver` is a **Directed Multigraph**.
This is richer than a Simple Graph.

*   **Simple Graph**: Edges are a Relation.
    *   `E ⊆ V × V`.
    *   Constraint: Between `A` and `B`, there is either *an* edge or *no* edge.
    *   Corresponds to `Hom : V → V → Prop` (Preorder).

*   **Directed Multigraph**: Edges are distinguishable entities.
    *   We can have distinct edges `f, g : A ⟶ B`.
    *   Corresponds to `Hom : V → V → Type v` (Category).

**Why do we need Multigraphs?**
Because Arrows represent **Processes**, not just connectivity.
The function `x ↦ x + 1` is different from `x ↦ 2 * x`, even though both connect `Nat` to `Nat`.

### 2.5 The Pedagogical Gap (Set Theory vs Type Theory)
Why is this confusing for beginners coming from standard math textbooks?

*   **In Set Theory (Textbooks)**: Everything is a Set.
    *   A Relation `R` is a subset of `V × V`. It's a set.
    *   A Hom-Set `Hom(A, B)` is a set of functions. It's a set.
    *   The distinction is purely **semantic** (how you use it).
    *   You don't have to "declare" whether it's a Property or Data.

*   **In Type Theory (Lean)**: Types are rigid.
    *   `Prop` (Logic) and `Type` (Data) are physically different universes.
    *   You **must** choose: Is `Hom(A, B)` a Proposition (Preorder) or Data (Category)?
    *   Lean forces you to confront the "Multigraph nature" of Categories immediately in the definition.
    *   This explicit rigorousness makes the learning curve steeper but the understanding deeper.

### 2.6 The Prop/Data Divide (The Preorder Degeneracy)

What happens when we choose `Hom : Prop`?
We inadvertently collapse the rich structure of a Category into the simpler structure of a **Preorder**.
This is a "Degeneracy" — we lose information.

**The Translation Dictionary**
Here is exactly how a Prop-Category translates to a Preorder:

1.  **Arrows become Relations**
    *   *Category*: `f : A ⟶ B` (A specific path).
    *   *Preorder*: `A ≤ B` (A fact that they are connected).
    *   *Why*: Proof Irrelevance forces all arrows `f, g` to be identical.

2.  **Identity becomes Reflexivity**
    *   *Category*: `id : A ⟶ A` (The "do nothing" path).
    *   *Preorder*: `A ≤ A` (Reflexivity axiom).

3.  **Composition becomes Transitivity**
    *   *Category*: `f ≫ g` (Chaining paths).
    *   *Preorder*: `A ≤ B ∧ B ≤ C → A ≤ C` (Transitivity axiom).

**The Isomorphism is Data**: `Category.{0} V ≅ Preorder V`

In Type Theory, an isomorphism is not just a property; it is a **Term** (a piece of data).
Constructing this isomorphism means defining a structure with four specific fields:

1.  **`toFun` (The Compiler)**
    *   Input: `C : Category V`
    *   Output: `Preorder V`
    *   *Implementation*: Maps `Hom` to `le`, `id` to `refl`, `comp` to `trans`.

2.  **`invFun` (The Decompiler)**
    *   Input: `P : Preorder V`
    *   Output: `Category V`
    *   *Implementation*: Maps `le` to `Hom`, `refl` to `id`, `trans` to `comp`.

3.  **`left_inv` (The Proof of Restoration)**
    *   Type: `∀ C, invFun (toFun C) = C`
    *   *Content*: A proof that compiling and decompiling gives back the *exact* original Category.
    *   *Why it works*: Since laws are `Prop`, they are definitionally equal. The data fields match exactly.

4.  **`right_inv` (The Proof of Consistency)**
    *   Type: `∀ P, toFun (invFun P) = P`
    *   *Content*: A proof that starting with a Preorder, converting to Category, and back, yields the original Preorder.

**Conclusion**:
The "Isomorphism" is this packet of 4 items. It explicitly proves that `Category.{0}` and `Preorder` are interchangeable in any mathematical context.
-/

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
## 4.3 Isomorphisms (`≅`) vs Equality (`=`)
In Category Theory, we almost never ask if `X = Y`. We ask if `X ≅ Y`.
An **Isomorphism** is data: a pair of maps `f, f⁻¹` that cancel out.

Syntax: `f : X ≅ Y` means f is an Isomorphism.
-/

def myIso : Nat ≅ Nat where
  hom := id
  inv := id
  -- We must prove they cancel.
  hom_inv_id := rfl
  inv_hom_id := rfl

/-!
## 4.4 Epimorphisms and Monomorphisms
How do we say "Injective" or "Surjective" without looking inside the object?
We use **Cancellation Laws**.

*   **Mono** (Injective-ish): Left-cancellable. `f ≫ a = f ≫ b → a = b`.
*   **Epi** (Surjective-ish): Right-cancellable. `a ≫ f = b ≫ f → a = b`.
-/

-- Example: The inclusion `Nat → Int` is a Mono.
example (f g : Int ⟶ Nat) (h : Nat ⟶ Int) (mono_h : Mono h) :
  f ≫ h = g ≫ h → f = g := by
  intro eq
  -- "Cancel h on the right"
  exact (cancel_mono h).mp eq

/-!
## 4.5 Functors: The Programs (`⥤`)
A **Functor** `F : C ⥤ D` is a program that transforms:
1.  Objects to Objects (`F.obj`)
2.  Morphisms to Morphisms (`F.map`)

It respects structure:
*   `F.map (f ≫ g) = F.map f ≫ F.map g`
*   `F.map (𝟙 X) = 𝟙 (F.obj X)`
-/

-- Identity Functor
#check 𝟭 Type

-- Composition of Functors
variable (F G : Type ⥤ Type)
#check F ⋙ G

/-!
---

# Part 5: Advanced Machinery (The Engine Room)

Now we descend into the engine room: Equality transport, Yoneda, and Adjunctions.

## 5.1 Path Induction: Logic (`=`) to Geometry (`⟶`)

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
## 5.2 Yoneda: Continuation Passing Style

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
## 5.3 Adjunctions: Foreign Function Interfaces

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
## 5.4 Limits: Data Structures
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

# 6. Conclusion

We have rebuilt Category Theory from the particles up:
1.  **Atoms**: Types, Terms, Universes.
2.  **Containers**: Structures and Classes.
3.  **Grammar**: Arguments (`{}`, `()`, `[]`) and Arrows (`→`, `⟶`).
4.  **Applications**: Using these to build Products, Adjunctions, and Embeddings.

You now possess the "Source Code" logic of the Lean Kernel.
-/

/-!
# 7. The Formal Proof (Executable)

We demonstrate the exact isomorphism between `Category.{0}` and `Preorder`.
This code compiles, proving the "0-byte" claim is a rigorous mathematical fact.
-/

section Proof

variable {V : Type}

/-!
### Note on Mathlib
Standard Mathlib `Category` specifies `Hom : V → V → Type v`.
To demonstrate the "Category in Prop" described in the text, we define `PropCategory`
where `Hom` lands in `Prop` (`Sort 0`).
-/

structure PropCategory (V : Type) where
  Hom : V → V → Prop
  id (a : V) : Hom a a
  comp {a b c : V} : Hom a b → Hom b c → Hom a c
  -- Laws are implicit because Hom is Prop (Subsingleton)

-- 1. Forward Map: PropCategory -> Preorder
def propCatToPreorder (C : PropCategory V) : Preorder V where
  le a b := C.Hom a b
  le_refl a := C.id a
  le_trans a b c f g := C.comp f g

-- 2. Backward Map: Preorder -> PropCategory
def preorderToPropCat (P : Preorder V) : PropCategory V where
  Hom a b := P.le a b
  id a := P.le_refl a
  comp f g := P.le_trans _ _ _ f g

-- 3. The Isomorphism (Equivalence)
def propCategoryIsoPreorder : PropCategory V ≃ Preorder V where
  toFun := propCatToPreorder
  invFun := preorderToPropCat
  left_inv := by
    intro C
    cases C
    dsimp [propCatToPreorder, preorderToPropCat]
  right_inv := by
    intro P
    dsimp [propCatToPreorder, preorderToPropCat]
    -- Use Extensionality for Preorders (equality is determined by 'le')
    apply Preorder.ext
    intro a b
    rfl

end Proof
