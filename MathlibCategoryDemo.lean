import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.List.Basic
import Mathlib.CategoryTheory.Opposites -- Required for unop

open CategoryTheory
open Opposite -- For unop

/-!
# Category Theory in Lean 4: The Computational Trinity (Ultra-Deep Edition)

This file is a "Masterclass" in **Formalized Category Theory**.
It peels back the layers of syntax to reveal the assembly code of the Lean Kernel.

## The Review: The Trinity
| Logic | Type Theory | Category Theory |
| :--- | :--- | :--- |
| Prop | Type | Object |
| Proof | Program | Morphism |
| Eq | Path | Diagram |

---

# 1. The Elaborator and The Unifier

How does Lean know that `Type` is a Category?
It uses **Type Class Synthesis**.

## 1.1 Elaboration
When we write `Category Type`, Lean's Elaborator asks the **Unifier** to resolve the instance.
The Unifier searches for a declared instance that matches the signature.

## 1.2 Transparency and Reducibility
The Unifier has different "Vision Modes" (Transparency settings):
1.  **Reducible (`abbrev`)**: Transparent. The unifier unfolds these immediately.
2.  **Semireducible (`def`)**: Translucent. Unfolded only if necessary for a match.
3.  **Irreducible (`opaque`)**: Opaque. Never unfolded during search.

This is why we used `abbrev MySource` in previous versions. If it were `opaque`,
the Type Class synthesis might fail to find instances for `Nat` attached to `MySource`.
-/

-- Kernel Inspection: Ask the Synthesizer to show us the instance.
#synth LargeCategory Type

-- Kernel Inspection: Verify the universe levels.
-- Type is in `Type 1`. Its objects are in `Type 0`.
#check LargeCategory.{0} Type

/-!
# 2. Path Induction: The Bridge from Logic to Geometry

In Logic, equality ($A = B$) allows us to "transport" proofs.
In Category Theory, if $X = Y$, we should be able to turn that equality into a Morphism $X \to Y$.

## 2.1 The `Eq` Type
`Eq` is an **Inductive Type**. It has exactly one constructor: `refl a : a = a`.
To use an equality `h : a = b`, we use **Path Induction** (Recursion on `Eq`).
This is fundamentally what the `rw` (rewrite) tactic does.

## 2.2 `eqToHom`: The Implementation
We define manual transport.
Mathematically: "Since X is Y, the Identity on X is a map X to Y".
Kernel: We match on `p`. Since the *only* possible value is `refl`, we just return `𝟙 X`.
-/

def myEqToHom {X Y : Type} (p : X = Y) : X ⟶ Y :=
  match p with
  | rfl => 𝟙 X

-- Application:
example : Nat ⟶ Nat := myEqToHom rfl

/-!
# 3. The Yoneda Lemma: The Assembly Language of Categories

The Yoneda Lemma is often called the hardest trivial thing in math.
In Computer Science terms, it is **Continuation Passing Style (CPS)**.

## 3.1 The Philosophy
How do you know who you are?
*   **Direct Style**: "I am the integer 5."
*   **CPS / Yoneda**: "I am the thing that, if you give me a function `Int -> R`, I will give you an `R`."
    $(Int \to R) \to R$.

In Categories: An object $X$ is completely determined by the set of morphisms *into* it (or *out of* it).

## 3.2 The Covey of Morphisms (Contravariant)
The Yoneda Embedding maps an object $X$ to the functor `Hom(-, X)`.
`X` $\mapsto$ `fun Y => (Y ⟶ X)`.

If we know all ways to map *into* $X$, we know $X$.
-/

-- We define the type signature effectively.
-- Ideally we would use Mathlib's `yoneda`, but we define the *mechanic* here.
def YonedaEmbedding (X : Type) : (Type)ᵒᵖ ⥤ Type where
  obj Y := (unop Y) ⟶ X
  map f := fun (g : (unop _) ⟶ X) => f.unop ≫ g
  map_id := by
    -- Kernel View: The lambda `\g. id ≫ g` reduces to `\g. g` via Identity Law.
    intros; dsimp [CategoryStruct.id]; funext; simp
  map_comp := by
    -- Kernel View: The lambda `\h. (f ≫ g) ≫ h` matches `\h. f ≫ (g ≫ h)` via Associativity.
    intros; dsimp [CategoryStruct.comp]; funext; simp

/-!
# 4. Kernel Reduction: Seeing the Matrix

We use `#reduce` to force the Kernel to evaluate terms to their normal form.
WARNING: This is computationally expensive. It performs full $\beta$-reduction.

## 4.1 Reducing Functors
Let's see what `listFunctor` actually *is* to the Kernel.
-/

def listFunctor : Type ⥤ Type where
  obj X := List X
  map f := List.map f
  map_id X := by dsimp [CategoryStruct.id]; funext l; simp
  map_comp f g := by dsimp [CategoryStruct.comp]; funext l; simp [List.map_map]

-- KERNEL INSPECTION:
-- Reduce the application of the functor's map to a concrete list.
-- The Kernel should output `[2, 3]`.
#reduce (listFunctor.map (fun x => x + 1)) [1, 2]

/-!
# 5. Universal Properties as "Holes"

A Universal Property specifies an object by describing the "Shape" of a hole in a diagram.
The Product $A \times B$ fills the hole in the diagram with $A$ and $B$.

## 5.1 The Logic of `Prop.ext` vs `funext`
In the Ultra-Deep proof below, we verify the Product Property.
We explicitly highlight the usage of **Extensionality Axioms**.
Lean's Kernel is "Intensional" (based on definitions), but we add axioms (`funext`, `propext`)
to make it behave "Extensionally" (based on behavior).
-/

example {Z A B : Type} (f : Z ⟶ A) (g : Z ⟶ B) :
  ∃! (u : Z ⟶ A × B), (u ≫ Prod.fst = f) ∧ (u ≫ Prod.snd = g) := by
  -- Candidate construction
  refine ⟨fun z => (f z, g z), ⟨?_, ?_⟩, ?_⟩

  -- Existence: Pure definitional reduction
  · dsimp [CategoryStruct.comp]; rfl
  -- Note: `rfl` works here because `(f z, g z).1` reduces to `f z` via **Iota Reduction** (Projection).
  · dsimp [CategoryStruct.comp]; rfl

  -- Uniqueness: The heavy lifting
  · intro v h
    -- v is an unknown function. We can't reduce it.
    -- We must use Extensionality.
    funext z -- "Two functions are equal if their outputs are equal"
    apply Prod.ext -- "Two pairs are equal if their components are equal"

    -- Subgoal 1: Left Component
    · have h1 := h.1
      -- `h1` says `v ≫ fst = f`.
      -- `congrFun h1 z` says `(v ≫ fst) z = f z`.
      -- `dsimp` at `(v ≫ fst) z` yields `(v z).1`.
      exact congrFun h1 z

    -- Subgoal 2: Right Component
    · have h2 := h.2
      exact congrFun h2 z

/-!
# 6. Conclusion: The Machine

We have seen that a "Category" in Lean is:
1.  A **Type Class** (Interface resolution).
2.  Parametrized by **Universes** (Logic vs Algebra).
3.  Governed by **Propositions** (Erasable Laws).
4.  Operated on by **Functors** (Programs).
5.  Verified by **Extensionality** (Behavioral Equality).

This is the machine that powers Modern Formalized Mathematics.
-/
