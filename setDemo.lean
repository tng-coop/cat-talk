import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

-- 1. The Real Set Equality
-- In Lean, Set is just a predicate.
-- If you move (α : Type) to the right, it becomes a "For All" (∀) statement.
-- The proof must now be a function (lambda) that takes 'α' as input.
example : ∀ (α : Type), (Set α) = (α → Prop) := fun _ => rfl
-- 1a. Universal Quantification = PI TYPE (Dependent Function)
-- This `∀ (α : Type), ...` IS a Pi Type.
-- Standard Notation: Π α : Type . (Set α = ...)   <-- Uses a DOT (.)
-- Lean Syntax:       ∀ (α : Type) , (Set α = ...)   <-- Uses a COMMA (,)
--
-- Syntax Anatomy:  ∀ (binder), (return_type)
--   - ∀ (α : Type)  : The BINDER (Input).
--   - ,             : The SEPARATOR (corresponds to the dot in Π notation).
--   - (Set α) = ... : The BODY (Output Type).

example : ∀ (α : Type), (Set α) = (α → Prop) := fun _ => rfl
-- 1. Set Builder Notation
example : (Set Nat) := {n | n % 2 = 0}
-- 2. Lambda (Predicate) Notation
example : (Set Nat) := fun n => n % 2 = 0

-- They are EXACTLY the same. Set Builder is just syntax sugar for the Lambda.
example : {n | n % 2 = 0} = (fun m : Nat => m % 2 = 0) := rfl

-- Alpha Equivalence: Lean IGNORES variable names.
-- To Lean's Kernel, 'a' and 'b' are just "Argument #1".
example : (fun a : Nat => a + 1) = (fun b : Nat => b + 1) := rfl
-- Style Note:
-- 1. Use `Nat → Nat` when the return type DOES NOT depend on the input (Simple functions).
-- 2. Use `∀ (n : Nat), Fin n` when the return type DOES depend on the input (Dependent types).
-- 3. You CAN use `∀ (n : Nat), Nat` just to name the variable for documentation,
--    but standard style prefers `Nat → Nat` in that case.

-- Both compile to the same thing:
example : Nat → Nat := fun _ => 0
example : ∀ (_ : Nat), Nat := fun _ => 0

-- 1b. Parameter Style (Syntactic Sugar)
-- Here we put "(α : Type)" on the left as a parameter.
-- Lean AUTOMATICALLY moves it to the right to create the "∀".
-- Lean AUTOMATICALLY adds the lambda "fun α =>" to the proof.
-- Result: They mean the EXACT same thing.
example (α : Type) : (Set α) = (α → Prop) := rfl
example : (Set Nat) = (Nat → Prop) := rfl
example (n : Nat) : Fin n = Fin n := rfl
-- Universe Levels in Lean:
-- Nat : Type      (Nat lives in Type)
-- Type : Type 1   (Type lives in Type 1)

-- 1. Set of ordinary types (Set Type)
-- The elements 'α' are types like Nat, Bool, etc.
example : Set Type := fun α => α = Nat

-- 2. Set of "Big" Types (Set (Type 1))
-- The elements 'α' are types like Type, Prop, etc.
-- Nat is too small to be here! Use 'Type' instead.
-- 3. Set of "Huge" Types (Set (Type 10))
-- You can go as high as you want!
-- This set contains elements that live in Type 10.
-- 'Type 9' lives in Type 10, so it fits.
example : Set (Type 10) := { Type 9 }
example : Set (Nat) := {0 }

-- Yes! {0} IS a function.
-- {0} means "The set containing only 0".
-- As a function, it means "is the input equal to 0?".
example : ({0} : Set Nat) = (fun n : Nat => n = 0) := rfl

-- UNIVERSE RULE FOR SETS:
-- Because Set α := α → Prop
-- TERMINOLOGY NOTE: "Set" has two meanings!
-- 1. The Lean Type Constructor (`Set α`):
--    This is the TOOL. It works at ALL levels.
--    `Set Nat`, `Set Type`, `Set (Type 10)` are all created with this tool.

-- 2. The Mathematical Jargon ("Set" vs "Class"):
--    Mathematicians distinguish by size:
--    - "Small Set" (Lives in Type 0): e.g., Set Nat. Defined as `Set Nat`.
--    - "Large Class" (Lives in Type 1): e.g., Set Type. Defined as `Set Type`.
--    So `Set Type` is TECHNICALLY a "Class", even though we use the `Set` keyword to build it!

-- Explanation:
-- `List` takes a Type (e.g., `List Nat`).
-- `Fin` takes a Value (e.g., `Fin 3`).
-- `a : Nat` is a Value, so `List a` is invalid, but `Fin a` is valid.

-- 2. Notation
-- We can use the standard notation from Mathlib
def Evens : Set Nat := { n | n % 2 == 0 }
def SmallNums : Set Nat := { n | n < 5 }

-- 3. Membership
example : 4 ∈ Evens := by
  -- 4 ∈ Evens reduces to Evens 4 -> 4 % 2 == 0
  simp [Evens]

example : 3 ∈ SmallNums := by
  simp [SmallNums]

-- 4. Operations
def UnionExample : Set Nat := Evens ∪ SmallNums

example : 4 ∈ UnionExample := by
  -- Unfold definitions. Simp handles the logic automatically.
  simp [UnionExample, Evens, SmallNums]

def InterExample : Set Nat := Evens ∩ SmallNums

example : 0 ∈ InterExample := by
  -- Unfold definitions. Simp handles the logic automatically.
  simp [InterExample, Evens, SmallNums]

-- 5. Set Extensionality
-- Two sets are equal if they have the same elements
example : ({1, 2} : Set Nat) = {2, 1} := by
  ext x
  simp
  rw [or_comm]
