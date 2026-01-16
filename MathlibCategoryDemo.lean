import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Category Theory in Lean 4: The Computational Trinity

This file implements Category Theory concepts in Lean 4, demonstrating the deep connection
known as the **Computational Trinity** (Curry-Howard-Lambek correspondence).
Theoretical concepts are mapped to code as follows:

| Logic (Propositions) | Type Theory (Computation) | Category Theory (Structure) | Implementation in this File |
| :--- | :--- | :--- | :--- |
| **Proposition** ($P$) | **Type** ($T$) | **Object** ($A$) | `Type` (or `MySource`) |
| **Proof** ($P \implies Q$) | **Program** ($f : T \to U$) | **Morphism** ($f : A \to B$) | `myMorphism` |
| **Equivalence** ($\iff$) | **Isomorphism** ($\simeq$) | **Isomorphism** ($\cong$) | `Nat ≅ Nat` |
| **Conjunction** ($\land$) | **Product Type** ($\times$) | **Product Object** ($\times$) | (Implicit in `Prod`) |
| **Disjunction** ($\lor$) | **Sum Type** ($\oplus$) | **Coproduct Object** ($\amalg$) | (Implicit in `Sum`) |
| **Simplification** | **Reduction/Computation** | **Commuting Diagram** | `rfl`, `simp`, `rewriting` |

This file focuses on the **Category Theory** column, realized via the **Type Theory** column.

---

# Rigorous Foundations (Expanded)

This document provides a comprehensive, formal introduction to the implementation of
Category Theory in Mathlib. It focuses on the Type Theoretic definitions,
Universe Polymorphism, and the Axiomatic Structure of the library.

## 1. The Hierarchy of Structure

In Mathlib, categorical structures are built using a **Type Class Hierarchy**.
This design separates the raw data of the graph from the algebraic operations,
and the operations from the laws that govern them. This is crucial for
definitional logical properties and type synthesis.

### 1.1 Quiver (The Data Layer)
At the lowest level, we have a `Quiver`. In combinatorics, this is known as a
**Directed Multigraph**. It defines connectivity but no algebra.
*   **Definition**: A type class `Quiver.{v} (V : Type u)`.
*   **Structure**: It provides a type family `Hom : V → V → Sort v`.
*   **Meaning**: For any two objects `a` and `b`, `Hom a b` is a Type (or Sort) representing
    the set of "arrows" between them.
*   **Notation**: `a ⟶ b` (unicode `\hom`).

### 1.2 CategoryStruct (The Algebraic Layer)
`CategoryStruct` extends `Quiver` by endowing the graph with algebraic operations.
It introduces the concept of "paths" of length 0 and length 2.
*   **Identity (`id`)**: For every object `X`, there is a distinguished morphism `𝟙 X : X ⟶ X`.
    This represents a "path of length 0" or "staying still".
*   **Composition (`comp`)**: A binary operation that concatenates arrows.
    `comp : (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)`.
*   **Notation**: `𝟙 X` (`\b1`) and `f ≫ g` (`\gg`).
*   **Note**: At this layer, **Associativity is NOT required**. `(f ≫ g) ≫ h` and `f ≫ (g ≫ h)`
    are distinct terms unless we add axioms.

### 1.3 Category (The Axiomatic Layer)
`Category` extends `CategoryStruct` by imposing the **Laws** (Axioms).
These laws convert the "Algebra of Arrows" into a proper Category.
*   **Identity Laws**:
    *   `id_comp`: `𝟙 X ≫ f = f` (Left Unit).
    *   `comp_id`: `f ≫ 𝟙 Y = f` (Right Unit).
*   **Associativity**:
    *   `assoc`: `(f ≫ g) ≫ h = f ≫ (g ≫ h)`.
*   **Type Theory Implication**: These axioms are **Propositions** (`Prop`).
    An instance of `Category` must provide **proofs** that these equalities hold.
    In Constructive Type Theory, these proofs allow us to **rewrite** terms, treating
    differently parenthesized paths as the same object.

-/

open CategoryTheory

/-!
## 2. Universe Management: Polymorphism and Hierarchy

Lean relies on a hierarchy of Universes `Sort u` (where `Type u = Sort (u+1)`).
Category Theory in Mathlib is **Universe Polymorphic**, meaning it can handle
categories of any size relative to their constituent objects.

### 2.1 The Signature: `Category.{v} (C : Type u)`
There are two Universe parameters at play:
1.  `u`: The universe level of the **Objects** (`C : Type u`).
2.  `v`: The universe level of the **Hom-sets** (`Hom X Y : Type v`).

### 2.2 Small Categories (`u = v`)
A category is **Small** if the collection of arrows is the "same size" as the collection of objects.
*   **Set Theory Analog**: The objects form a Set, and the morphisms form a Set.
*   **Mathlib**: `SmallCategory (C : Type u)` is short for `Category.{u} C`.
*   **Example**: `FinCategory` (Finite categories), Groups (as categories).

### 2.3 Large Categories (`u = v + 1`)
A category is **Large** if the objects live in a higher universe than the arrows.
*   **Set Theory Analog**: The objects form a Proper Class, but the morphisms between any two
    specific objects still form a Set ("Locally Small").
*   **Mathlib**: `LargeCategory (C : Type (u+1))` is short for `Category.{u} C`.
*   **Example**: `Type`, `Group`, `TopologicalSpace`.

See below: `Type` is the category where Objects are Types (in `Type 1`) and Morphisms are
Functions (in `Type 0`). Thus it is `LargeCategory`.
-/
example : LargeCategory Type := inferInstance

/-!
## 3. The Category of Types: Concrete Implementation

In the Category `Type`, the abstract structures map directly to Lean's internal primitives.

### 3.1 The Hom-set
The type `X ⟶ Y` is defined as `X → Y` (the built-in function type).
This is a **Definitional Equality** (`=`). The type checker treats them as identical.
This is why we can apply a "morphism" `f` directly to an "object" `x` via `f x`.

### 3.2 Reducibility and `abbrev`
We define `MySource` using `abbrev` to ensure **Transparency**.
*   `def`: Creates a new constant that wraps the value (Opaque).
    Lean will not automatically unfold `def`s during Type Class Resolution.
*   `abbrev`: Creates a definition capable of being immediately unfolded by the kernel.
    This is critical when we want Mathlib to recognize `MySource` as `Nat` to find instances like `ToString`.
-/
abbrev MySource : Type := Nat
abbrev MyTarget : Type := String

/--
A specific morphism instance.
Type Check: `toString` has type `Nat → String`.
Categorical Context: `MySource ⟶ MyTarget` expects `Nat → String`.
Match: Exact.
-/
def myMorphism : MySource ⟶ MyTarget := toString

/-!
## 4. Composition and Duality

### 4.1 Diagrammatic Order (`≫`)
Mathlib uses "Diagrammatic" (left-to-right) composition order.
`f ≫ g` matches the visual flow of arrows: `A --f--> B --g--> C`.
This contrasts with standard Algebra notation `g ∘ f` ("Applied Order").
*   In `Type`: `(f ≫ g) x` reduces to `g (f x)`.

### 4.2 The Opposite Category (`Cᵒᵖ`)
A fundamental concept in Category Theory is **Duality**.
For every category $C$, there is an Opposite Category $C^{op}$.
*   **Objects**: Same as $C$.
*   **Morphisms**: `Hom_op X Y` is defined as `Hom_C Y X`.
*   **Composition**: `f ≫_op g` is defined as `g ≫_C f`.
This is handled automatically in Mathlib via the `Opposite` type.
-/

-- Verification: Composition Laws holding definitionally.
-- Because `Type` is a "Constructive" category built on functions,
-- the laws hold by `rfl` (Reflexivity) because the underlying lambda terms are identical.
-- `id ≫ f` = `fun x => f (id x)` = `fun x => f x` = `f`.
example : 𝟙 MySource ≫ myMorphism = myMorphism := rfl
example : myMorphism ≫ 𝟙 MyTarget = myMorphism := rfl

/-!
## 5. Isomorphisms: Witnessing Equality

In Type Theory, stating that two objects are "equal" (`=`) is a very strong statement
that is often unprovable or "evil" (violates the principle of equivalence).
Category Theory replaces equality with **Isomorphism** (`≅`).

### 5.1 Structure of `Iso`
An Isomorphism is not a Prop; it is a **Datum**. It is a record containing:
1.  `hom`: The map $A \to B$.
2.  `inv`: The map $B \to A$.
3.  `hom_inv_id`: A **proof** that doing `hom` then `inv` is identity.
4.  `inv_hom_id`: A **proof** that doing `inv` then `hom` is identity.

This structure allows us to *compute* with isomorphisms (e.g., reversing them) and
transport properties between isomorphic objects.
-/

def natIsoNat : Nat ≅ Nat where
  hom := 𝟙 Nat
  inv := 𝟙 Nat
  hom_inv_id := Category.id_comp (𝟙 Nat) -- Proof by Axiom Application
  inv_hom_id := Category.id_comp (𝟙 Nat)

/-!
## 6. Functors: Homomorphisms of Categories

A `Functor` maps the structure of one category to another. It is the
"Morphism of Categories".

### 6.1 The Components
1.  **Object Map** (`obj`): Maps objects $C \to D$.
2.  **Morphism Map** (`map`): Maps arrows $(X \to Y) \to (F(X) \to F(Y))$.

### 6.2 The Laws (Structure Preservation)
A functor must preserve the algebraic structure defined in `CategoryStruct`:
1.  **Identity Preservation**: `map (id) = id`.
2.  **Composition Preservation**: `map (f ≫ g) = map f ≫ map g`.

### 6.3 Implementation Details
Below, we prove that `List` forms a valid Functor from `Type` to `Type`.
Note the usage of `dsimp` (Definitional Simplification).
*   Why `dsimp`? It creates a stronger tactic state by exposing the underlying lambda terms
    of `CategoryStruct.id` and `.comp`, allowing the simplifier to see that
    `𝟙 X` is transparently `id`.
-/

def listFunctor : Type ⥤ Type where
  obj X := List X
  map f := List.map f
  map_id X := by
    -- Goal: List.map (𝟙 X) = 𝟙 (List X)
    -- 1. Unfold 'Structure' definitions to 'Type' definitions.
    --    This reveals that `𝟙 X` is just `id`.
    dsimp [CategoryStruct.id]
    -- 2. Use `funext` (Function Extensionality) to compare function definitions input-wise.
    funext l
    -- 3. Apply standard library lemmas (`List.map_id`).
    simp
  map_comp f g := by
    -- Goal: List.map (f ≫ g) = List.map f ≫ List.map g
    -- 1. Unfold structure to see this is `List.map (g ∘ f)`.
    dsimp [CategoryStruct.comp]
    funext l
    -- 2. Apply `List.map_map` which states `map g (map f l) = map (g ∘ f) l`.
    simp [List.map_map]

/-!
## 7. The Philosophy of `Prop` vs `Data`

A critical distinction in this file (and Mathlib) is between things that are **Data**
and things that are **Propositions**.

| Concept | Type | Nature |
| :--- | :--- | :--- |
| `Category` | Type Class | **Data** (Contains fields like `Hom`) |
| `id`, `comp` | Functions | **Data** (Executable code/terms) |
| `assoc` | Prop | **Proof** (Irrelevant for runtime, crucial for logic) |
| `Functor` | Structure | **Data** (Contains `obj` and `map` functions) |
| `map_comp` | Prop | **Proof** (Guarantee of correctness) |

This separation allows standard code (like `List.map`) to be used as Categorical Data
by simply "bundling" it with the necessary proofs.
-/
