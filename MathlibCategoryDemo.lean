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
-- SYNTAX: `.{0}`
-- This is **Explicit Universe Instantiation**.
-- `LargeCategory` is polymorphic: `LargeCategory.{u} (C : Type (u+1))`.
-- Normally Lean infers `u`. Here, we force `u = 0`.
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

-- SYNTAX: `{X Y : Type}` vs `(p : X = Y)`
-- `{...}`: **Implicit Argument**. Lean infers X and Y from the type of `p`.
-- `(...)`: **Explicit Argument**. You must provide `p`.
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
-- SYNTAX: `(Type)ᵒᵖ` and `.unop`
-- `(Type)ᵒᵖ`: Type-level function application `Opposite Type`.
-- `.unop`: **Dot Notation**. `f.unop` is syntactic sugar for `Opposite.unop f`.
-- Lean finds `Opposite.unop` because `f` has type `(Type)ᵒᵖ`.
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
  -- SYNTAX: `refine ⟨...⟩` and `?_`
  -- `⟨x, y, z⟩`: **Anonymous Constructor**. Lean infers we are building an `ExistsUnique` structure.
  -- `?_`: **Hole** (Meta-variable). Creates a new goal for us to solve later (specifically the `by` blocks below).
  refine ⟨fun z => (f z, g z), ⟨?_, ?_⟩, ?_⟩

  -- SYNTAX: `·` (Bullet) and `;` (Semicolon)
  -- `·`: **Focus**. Isolates the current goal. Errors if we don't finish the goal inside.
  -- `;`: **Sequencing**. `dsimp; rfl` means "run dsimp, THEN run rfl on all resulting goals".
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
# 6. Proof Engineering: The "Opposite" Wrapper

Why did we need `import Mathlib.CategoryTheory.Opposites`?
Why does `Open Opposite` fail if we don't?

## 6.1 The Danger of Type Synonyms
We could define:
`def MyOpposite (α : Type) := α`
This is a **Type Synonym**. It is definitionally equal to `α`.

## 6.2 The Instance Loop Problem
If `Category MyOpposite` is definitionally `Category Type`, the Instance Synthesizer gets confused.
When looking for `Category X`, it might try `Category (MyOpposite X)`.
If they are the same, it enters an **Infinite Loop**.

## 6.3 The Solution: Structures as Wrappers
Lean solves this by using a `structure` (or `inductive` type) wrapper:
`structure Opposite (α : Type) := (unop : α)`

This creates a **New Type**. The Kernel sees `Opposite α` and `α` as distinct.
This prevents loops and allows us to attach different instances to `α` vs `αᵒᵖ`.
This is "Proof Engineering": designing types for the Compiler, not just the Mathematician.
-/

/-!
# 7. Adjunctions: The Function Calls of the Universe

An Adjunction is a pair of Functors $L \dashv R$ that are "inverse-ish".
But computationally, they are **Translation Mechanisms**.

## 7.1 Currying as the Archetype
The most famous adjunction is Currying.
Problem: Map a pair $(A, B)$ to $C$.
Translation: Map $A$ to a function $(B \to C)$.

We implement this Isomorphism explicitly.
-/

def curryingAdjunction {A B C : Type} : (A × B ⟶ C) ≅ (A ⟶ (B ⟶ C)) where
  hom f := fun a b => f (a, b)
  inv g := fun p => g p.1 p.2
  hom_inv_id := by
    -- Logic: \f. (\p. f p.1 p.2) should be f.
    funext f; funext p;
    -- Iota reduction on p: p is (p.1, p.2)
    cases p; rfl
  inv_hom_id := by
    -- Logic: \g. \a \b. g a b should be g.
    funext g; funext a; funext b; rfl

/-!
## 7.2 The Philosophy
Adjunctions allow us to solve a problem in a "Hard" category (Product Space)
by moving it to an "Easy" category (Function Space), or vice versa.
It is the Category Theory equivalent of a **Foreign Function Interface (FFI)**.
-/

/-!
# 8. Limits: Data Structures from Universal Properties

A "Limit" (like a Product, Pullback, or Equalizer) is often taught as a property.
In Lean, it is a **Data Structure**.

## 8.1 The Cone
A `Cone` over a diagram (here, just two objects X and Y) is:
1.  An Apex object `pt`.
2.  Maps to X and Y.
-/

structure MyCone (X Y : Type) where
  pt : Type
  π₁ : pt ⟶ X
  π₂ : pt ⟶ Y

/-!
## 8.2 The Terminal Cone
The Product `X × Y` is the "Best" Cone.
Every other cone maps uniquely into it.
This "Mapping In" property is what makes it a **Terminal Object** in the Category of Cones.
-/

def productCone (X Y : Type) : MyCone X Y where
  pt := X × Y
  π₁ := Prod.fst
  π₂ := Prod.snd

-- The Universal Property essentially says:
-- "For any `c : MyCone X Y`, there is a unique `lift : c.pt ⟶ (productCone X Y).pt`..."

/-!
# 9. Conclusion: The Galactic View

We have traversed from the atom (`Prop`, `Type`, `Eq`) to the galaxy (`Adjunction`, `Limit`).
1.  **Elaboration**: The engine that finds our tools.
2.  **Yoneda**: The assembly code that defines identity by interaction.
3.  **Adjunctions**: The bridges that transport problems between worlds.
4.  **Limits**: The optimal data structures satisfying universal constraints.

This is the code that runs the universe.
-/
