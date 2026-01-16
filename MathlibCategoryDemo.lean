import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.List.Basic

/-!
# Category Theory in Lean 4: The Computational Trinity (Definitive Edition)

This file implements Category Theory concepts in Lean 4, demonstrating the deep connection
known as the **Computational Trinity** (Curry-Howard-Lambek correspondence).
It is designed to be read not just as code, but as a textbook on **Formalized Mathematics**.

## The Trinity

| Logic (Propositions) | Type Theory (Computation) | Category Theory (Structure) |
| :--- | :--- | :--- |
| **Proposition** ($P$) | **Type** ($T$) | **Object** ($A$) |
| **Proof** ($P \implies Q$) | **Program** ($f : T \to U$) | **Morphism** ($f : A \to B$) |
| **Equivalence** ($\iff$) | **Isomorphism** ($\simeq$) | **Isomorphism** ($\cong$) |
| **Simplification** | **Reduction/Evaluation** | **Commuting Diagram** |

---

# 1. The Hierarchy of Categorical Structure

Mathlib uses a **Bundled Type Class** approach. This differs from "Structure" based approaches
in conventional programming. We do not just "have" a category; a type "is" a category.

## 1.1 Quiver: The Pre-Category
The foundation is the `Quiver` type class.
*   **Mathematical Object**: A Directed Multigraph.
*   **Type Signature**: `Quiver.{v} (V : Type u)`
    *   `V` is the type of Vertices (Objects).
    *   `Hom : V → V → Sort v` is the type family of Edges (Morphisms).
*   **Deep Concept**: Why `Sort v`?
    *   If `v = 0`, `Hom a b` is a `Prop`. This models a **Preorder** (at most one arrow).
    *   If `v = 1`, `Hom a b` is a `Type`. This models a standard **Locally Small Category**.
    *   This polymorphism allows Mathlib to reuse the same structure for logic and algebra.

## 1.2 CategoryStruct: The Algebraic Skeleton
`CategoryStruct` extends `Quiver` by adding the *operations* without the *laws*.
*   `id (X : V)`: The polymorphic identity arrow.
*   `comp (f : X ⟶ Y) (g : Y ⟶ Z)`: The composition operator.
*   **Notation**: `f ≫ g` (Diagrammatic).
    *   Note: Standard math uses $g \circ f$ (Applicative). Mathlib chose Diagrammatic because
        it matches the flow of data types in programming and diagrams naturally.

## 1.3 Category: The Lawful Algebra
`Category` adds the axioms (Propositions).
*   `assoc`: `(f ≫ g) ≫ h = f ≫ (g ≫ h)`
*   `id_comp`, `comp_id`: Identity laws.

**Why are these `Prop`?**
In Lean, `Prop` is proof-irrelevant. It effectively vanishes at runtime.
This means a Category is *computationally* just a Graph with composition.
The laws are "Ghost Data" that the compiler checks but the runtime erases.
This makes the implementation maximally efficient.

-/

open CategoryTheory

/-!
# 2. Universe Polymorphism and the "Size" of Categories

This section explains the most complex part of Mathlib's design: Universes.

## 2.1 The Problem
Can a Category contain itself? (Russell's Paradox).
In Set Theory, we distinguish Sets vs Proper Classes.
In Type Theory, we distinguish `Type u` vs `Type (u+1)`.

## 2.2 The Solution
*   **Small Category**: `Category.{u} (C : Type u)`.
    *   Objects are in `Type u`.
    *   Morphisms are in `Type u`.
    *   "Set of objects and Set of morphisms".
*   **Large Category**: `Category.{u} (C : Type (u+1))`.
    *   Objects are in `Type (u+1)` (A "Class" of objects).
    *   Morphisms are in `Type u` (Locally Small).
    *   Example: `Type`. The collection of all types has type `Type 1`.
        But the function type `Nat → Nat` has type `Type 0`.

Mathlib solves this by parametrising `Category` with two universe levels: `Category.{v, u}`.
-/

-- We instantiate the Large Category of Types.
-- This tells Lean: "Treat the universe of Types as a Category where morphisms are Functions".
example : LargeCategory Type := inferInstance

/-!
# 3. The Concrete Category of Types

Here we bridge the gap between Abstract Category Theory and Concrete Programming.

## 3.1 Objects and Morphisms
In `Category Type`:
*   Objects are types (e.g., `Nat`, `String`, `List Int`).
*   Morphisms `X ⟶ Y` are *exactly* functions `X → Y`.
    *   This is a **Definitional Equality**. You can replace one with the other anywhere.
-/

abbrev MySource : Type := Nat
abbrev MyTarget : Type := String

/--
A morphism in `Type`.
Note the type annotation: `MySource ⟶ MyTarget`.
Under the hood, this is just `Nat → String`.
-/
def myMorphism : MySource ⟶ MyTarget := toString

/-!
## 3.2 Composition and Associativity
In `Type`:
*   `𝟙 X` reduces to `id` (the identity function).
*   `f ≫ g` reduces to `g ∘ f` (function composition).

**The Associativity Miracle**:
For functions, associativity is true **by definition** of lambda calculus.
`((f ≫ g) ≫ h) x` = `h (g (f x))`
`(f ≫ (g ≫ h)) x` = `h (g (f x))`
Since they reduce to the same term, `refl` suffices.
-/

example : 𝟙 MySource ≫ myMorphism = myMorphism := rfl
example : myMorphism ≫ 𝟙 MyTarget = myMorphism := rfl

/-!
# 4. Isomorphisms: The Constructive Interpretation

In Classical Math, isomorphism is property "there exists an inverse".
In Constructive Type Theory, isomorphism is **Data**. It is a structure.

## 4.1 The Structure `Iso`
An `Iso A B` contains:
1.  `hom : A ⟶ B`
2.  `inv : B ⟶ A`
3.  `hom_inv_id`: A proof that `hom ≫ inv = 𝟙 A`.
4.  `inv_hom_id`: A proof that `inv ≫ hom = 𝟙 B`.

This "bundling" of the inverse allows us to *compute* with it.
If we only knew "an inverse exists", we couldn't run it as a program.
-/

def natIsoNat : Nat ≅ Nat where
  hom := 𝟙 Nat
  inv := 𝟙 Nat
  hom_inv_id := Category.id_comp (𝟙 Nat)
  inv_hom_id := Category.id_comp (𝟙 Nat)

/-!
# 5. Functors: Morphisms of Categories

A Functor is a structure preserving the categorical algebra.

## 5.1 The Definition
*   `obj : C → D`: Transformation of objects.
*   `map : (X ⟶ Y) → (F(X) ⟶ F(Y))`: Transformation of morphisms.
*   `map_id`: Preservation of Identity.
*   `map_comp`: Preservation of Composition.

## 5.2 Deep Dive: The `List` Functor
We implement `List` as a functor.
The proofs use **Definitional Simplification (`dsimp`)**.
*   `dsimp`: Unfolds definitions (like `CategoryStruct.comp`) but performs no rewriting.
    It exposes the underlying lambda terms.
*   `simp`: Performs rewriting using lemmas (like `List.map_map`).
-/

def listFunctor : Type ⥤ Type where
  obj X := List X
  map f := List.map f
  map_id X := by
    -- 1. Reveal that categorical identity is function identity
    dsimp [CategoryStruct.id]
    -- 2. Reveal that functional identity effectively does nothing
    funext l; simp
  map_comp f g := by
    -- 1. Reveal that categorical composition is function composition
    dsimp [CategoryStruct.comp]
    funext l
    -- 2. Use the map_map lemma: map (g ∘ f) = map g ∘ map f
    simp [List.map_map]

/-!
# 6. Natural Transformations: Morphisms of Functors

Natural Transformations form the "arrows between arrows".
$\alpha : F \Longrightarrow G$.

## 6.1 The Naturality Square
For any $f: X \to Y$, the diagram must commute:
$$
\begin{array}{ccc}
F(X) & \xrightarrow{F(f)} & F(Y) \\
\downarrow \alpha_X & & \downarrow \alpha_Y \\
G(X) & \xrightarrow{G(f)} & G(Y)
\end{array}
$$
In code: `map f ≫ app Y = app X ≫ map f`.

## 6.2 Example: Safe Head
We transform `List` to `Option` via `head?`.
The naturality condition asserts:
"Taking the head then applying $f$" IS THE SAME AS "Applying $f$ to the list then taking the head".
This captures the essence of **Polymorphism** and **Parametricity**.
-/

-- Aux: Option Functor
def optionFunctor : Type ⥤ Type where
  obj X := Option X
  map f := Option.map f
  map_id X := by dsimp [CategoryStruct.id]; funext x; cases x <;> simp
  map_comp f g := by dsimp [CategoryStruct.comp]; funext x; cases x <;> simp

def safeHead : listFunctor ⟶ optionFunctor where
  app X := List.head?
  naturality X Y f := by
    -- Unfold everything to bare functions
    dsimp [CategoryStruct.comp, listFunctor, optionFunctor]
    funext l
    -- Verify for Empty and Cons cases
    cases l <;> simp

/-!
# 7. Universal Properties: The Logic of Unique Existence

This is the heart of Category Theory. Objects are defined by their **Relationship** to the universe.

## 7.1 The Product Specification
A Product $P$ is "The object that can simulate any pair of maps to A and B".
$\forall Z, \forall (f: Z \to A), (g: Z \to B), \exists! (u: Z \to P)...$

## 7.2 The Proof
We prove `Prod` (Tuple) satisfies this specification.
*   **Existence**: We construct the function `fun z => (f z, g z)`.
*   **Uniqueness**: We use `Prod.ext` (Extensionality).
    *   "If two pairs have the same components, they are the same pair."
*   **Function Extensionality**:
    *   "If two functions return the same values for all inputs, they are the same function."
    We must combine these two principles to prove uniqueness of the product map.
-/

example {Z A B : Type} (f : Z ⟶ A) (g : Z ⟶ B) :
  ∃! (u : Z ⟶ A × B), (u ≫ Prod.fst = f) ∧ (u ≫ Prod.snd = g) := by
  -- 1. Construct the solution term
  refine ⟨fun z => (f z, g z), ⟨?_, ?_⟩, ?_⟩

  -- 2. Proof of Existence (Commutativity)
  -- The definitional equality `(a, b).1 = a` makes this trivial by `rfl`.
  · dsimp [CategoryStruct.comp]; rfl
  · dsimp [CategoryStruct.comp]; rfl

  -- 3. Proof of Uniqueness
  · intro v h
    -- h contains proofs that v projects to f and g.
    -- We must show v IS `fun z => (f z, g z)`.
    funext z
    apply Prod.ext

    -- Left Component
    · have h1 := h.1
      replace h1 := congrFun h1 z -- "Apply" the function equality to z
      exact h1

    -- Right Component
    · have h2 := h.2
      replace h2 := congrFun h2 z
      exact h2
