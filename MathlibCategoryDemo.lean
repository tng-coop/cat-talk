import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.List.Basic

/-!
# Category Theory in Lean 4: The Computational Trinity (Hyper-Deep Edition)

This file is a treatise on **Formalized Category Theory**. usage of Mathlib is not just
API consumption; it is an exercise in Constructive Type Theory.

## The Computational Trinity
We define the correspondence precisely:

| Logic (Propositions) | Type Theory (Computation) | Category Theory (Structure) |
| :--- | :--- | :--- |
| **Proposition** ($P : Prop$) | **Type** ($T : Type u$) | **Object** ($A$) |
| **Proof** ($p : P$) | **Program** ($t : T$) | **Morphism** ($f : A \to B$) |
| **Equivalence** ($\iff$) | **Isomorphism** ($\simeq$) | **Isomorphism** ($\cong$) |
| **Equality** ($x = y$) | **Path** ($x =_T y$) | **Commuting Diagram** |

---

# 1. The Foundation: Lean's Logical Kernel

Before defining a Category, we must understand the "Soil" it grows in: The `Sort` Hierarchy.

## 1.1 The Hierarchy of Universes
Lean uses a non-cumulative hierarchy of universes to avoid Russell's Paradox.
*   `Sort 0` is `Prop`. This is the universe of **Propositions**.
    *   **Proof Irrelevance**: Any two proofs `p, q : P` are definitionally equal.
    *   **Use Case**: Categorical Axioms (Associativity, Identity Laws).
*   `Sort 1` is `Type 0`. This is the universe of **Datatypes** (Nat, List, Bool).
*   `Sort (u+1)` is `Type u`. This is the universe of **Types**.

## 1.2 The Master Key: Polymorphic Arrows
In Mathlib, the "Arrow" is defined in `Quiver` as:
`Hom : V → V → Sort v`

This single valid signature covers ALL cases:
*   **Logic (Preorder)**: `v = 0`. `Hom A B` is a `Prop`.
    *   `A ⟶ B` means $A \le B$. There is at most one arrow (the proof).
*   **Algebra (Category)**: `v = 1`. `Hom A B` is a `Type`.
    *   `A ⟶ B` is a Set of arrows. (e.g. Group homomorphisms).
*   **Higher Category**: `v > 1`. `Hom A B` is itself a Category.

-/

open CategoryTheory

/-!
# 2. Definitional Equality: The Ghost in the Machine

In `Category Type`, we rely heavily on **Definitional Equality** ($x \equiv y$).
This is different from **Propositional Equality** ($x = y$).

*   **Definitional ($x \equiv y$)**: The Kernel *knows* they are the same. `rfl` proves it.
    *   **Delta Reduction ($\delta$)**: Unfolding a function definition.
    *   **Beta Reduction ($\beta$)**: Applying a lambda `(\x. b) a` -> `b[x/a]`.
    *   **Iota Reduction ($\iota$)**: Reducing a recursor/match expression.
*   **Propositional ($x = y$)**: We must *prove* they are the same using axioms.

## 2.1 The Concrete Category `Type`
Mathlib Definition:
`instance : LargeCategory Type := { Hom := fun X Y => X → Y, ... }`

By **Delta Reduction**, `Hom X Y` reduces to `X → Y`.
This is why we can treat standard functions as morphisms without explicit casting.
-/

-- We explicitly instantiate the category to use its notation.
example : LargeCategory Type := inferInstance

abbrev MySource : Type := Nat
abbrev MyTarget : Type := String

/--
A morphism in `Type`.
Type signature: `MySource ⟶ MyTarget`
Kernel View:    `Nat → String`
Cost:           Zero (Definitional Alias)
-/
def myMorphism : MySource ⟶ MyTarget := toString

/-!
# 3. Axioms as "Ghost Data" (Prop Irrelevance)

A `Category` extends `CategoryStruct` (Data) with `Category` (Axioms).

*   `assoc : (f ≫ g) ≫ h = f ≫ (g ≫ h)`

In a runtime language (Haskell/Rust), associativity might affect memory layout.
In Lean, `assoc` has type `Prop`.
At runtime, **Propositions are erased**.
The compiler sees only the raw functions. The proof of associativity exists solely to
satisfy the Type Checker during compilation.
-/

-- Proof of associativity in Type is `rfl`.
-- Why? Because function composition is associative by Lambda Calculus Definition.
-- LHS: `\x => h (g (f x))`
-- RHS: `\x => h (g (f x))`
-- They are syntactically identical after Beta reduction.
example (f g h : MySource ⟶ MySource) : (f ≫ g) ≫ h = f ≫ (g ≫ h) := rfl

/-!
# 4. The "Evil" of Equality vs The Virtue of Isomorphism

In Category Theory, referring to "Equality of Objects" ($A = B$) is considered "**Evil**".
It violates the **Principle of Equivalence**: "Properties should be invariant under Isomorphism".

## 4.1 Constructive Isomorphism
In Classical Math: $A \cong B \iff \exists f, f^{-1}...$ (Prop)
In Constructive Type Theory (Mathlib): `A ≅ B` is a **Structure** (Data).

When we have `Nat ≅ Nat`, we strictly carry the data:
1.  Forward map (`id`)
2.  Backward map (`id`)
3.  Witnesses of inversion.

This allows us to **Execute** the isomorphism.
-/

def natIsoNat : Nat ≅ Nat where
  hom := 𝟙 Nat
  inv := 𝟙 Nat
  hom_inv_id := Category.id_comp (𝟙 Nat) -- Axiom application
  inv_hom_id := Category.id_comp (𝟙 Nat)

/-!
# 5. Functors and the Art of Simplification

Implementing a Functor requires proving that it commutes with identity and composition.
We use the Simplifier (`simp`) to automate this.

## 5.1 The Tactic State Explanation
In the `listFunctor` below, observe the tactic `dsimp`.

*   **Goal**: `List.map (f ≫ g) = List.map f ≫ List.map g`
*   `f ≫ g` is Categorical Composition.
*   `List.map f ≫ List.map g` is Categorical Composition.

`dsimp [CategoryStruct.comp]` acts as a **Kernel Lens**.
It forces the simplifier to Delta-Reduce `≫` to `∘`.
This transforms the goal into:
`List.map (g ∘ f) = List.map g ∘ List.map f`

Now `simp [List.map_map]` can match the pattern.
Without `dsimp`, the simplifier might get stuck on the opaque `≫` symbol.
-/

def listFunctor : Type ⥤ Type where
  obj X := List X
  map f := List.map f
  map_id X := by
    -- Kernel View: List.map (fun x => x) = (fun x => x)
    dsimp [CategoryStruct.id]
    funext l; simp
  map_comp f g := by
    -- Kernel View: List.map (fun x => g (f x)) = (fun x => g (List.map f x))
    dsimp [CategoryStruct.comp]
    funext l
    simp [List.map_map]

/-!
# 6. Natural Transformations: 2-Cells

Natural Transformations are the morphisms between functors.
$\alpha : F \Longrightarrow G$.

## 6.1 Parametricity
The `naturality` condition is the mathematical formalization of **Parametric Polymorphism**.
If a function `safeHead` works for *any* type `X` without inspecting `X`, it *must* be natural.
It cannot "react differently" to the values inside, because it doesn't know their type.

## 6.2 The Proof
We define `safeHead : List -> Option`.
Logic: `head?` respects `map`.
-/

def optionFunctor : Type ⥤ Type where
  obj X := Option X
  map f := Option.map f
  map_id X := by dsimp [CategoryStruct.id]; funext x; cases x <;> simp
  map_comp f g := by dsimp [CategoryStruct.comp]; funext x; cases x <;> simp

def safeHead : listFunctor ⟶ optionFunctor where
  app X := List.head?
  naturality X Y f := by
    -- Goal: listFunctor.map f ≫ safeHead.app Y = safeHead.app X ≫ optionFunctor.map f
    -- We reduce categorical composition to function composition using dsimp.
    dsimp [CategoryStruct.comp, listFunctor, optionFunctor]
    funext l
    -- We proceed by "Case Analysis" (Iota Reduction) on `l`.
    -- If l = [], both sides are none.
    -- If l = a::as, both sides are f(a).
    cases l <;> simp

/-!
# 7. Universal Properties and Extensionality

A Universal Property is a **Specification**.
For `Product`, the specification is:
"I am the unique object that factors maps to A and B".

## 7.1 Existence ($\exists$)
We find a candidate: `fun z => (f z, g z)`.
We prove it works using `rfl`.

## 7.2 Uniqueness ($\forall y, ... \implies y = u$)
We must prove that ANY function `v` satisfying the condition is equal to our candidate.
*   `v` is a function.
*   To prove Logic equality of functions, we use **Function Extensionality** (`funext`).
    `v = u \iff \forall x, v x = u x`.
*   To prove Logic equality of pairs, we use **Product Extensionality** (`Prod.ext`).
    `p = q \iff p.1 = q.1 \land p.2 = q.2`.

Combining these gives the rigorous proof.
-/

example {Z A B : Type} (f : Z ⟶ A) (g : Z ⟶ B) :
  ∃! (u : Z ⟶ A × B), (u ≫ Prod.fst = f) ∧ (u ≫ Prod.snd = g) := by
  -- 1. Provide the candidate witness
  refine ⟨fun z => (f z, g z), ⟨?_, ?_⟩, ?_⟩

  -- 2. Existence Proofs (Commutativity)
  -- Uses Delta Reduction (unfolding comp) and Beta Reduction (applying lambda).
  · dsimp [CategoryStruct.comp]; rfl
  · dsimp [CategoryStruct.comp]; rfl

  -- 3. Uniqueness Proof
  · intro v h
    -- h : v commutes with fst AND v commutes with snd
    funext z
    apply Prod.ext

    -- Left Projection Logic
    · have h1 := h.1
      -- Transform Function Equality (f = g) into Value Equality (f x = g x) via Congruence
      replace h1 := congrFun h1 z
      exact h1

    -- Right Projection Logic
    -- Note: We use `exact` which performs Unification to match the goal.
    · have h2 := h.2
      replace h2 := congrFun h2 z
      exact h2
