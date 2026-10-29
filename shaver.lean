import Mathlib.Data.Set.Basic

-- The Barber of Shaver Village
-- Paradox: "The barber shaves everyone who does not shave themselves."
-- Question: Does the barber shave himself?

-- In Set Theory notation:
-- Let R = { x | x ∉ x }  (The set of all sets that do not contain themselves)
-- Does R ∈ R?
-- If yes (R ∈ R) -> then R must satisfy the property (R ∉ R). Contradiction!
-- If no (R ∉ R) -> then R satisfies the property, so R ∈ R. Contradiction!

-- HOW LEAN PREVENTS THIS:

-- 1. Let's try to define "x ∈ x" (Self-Membership).
-- Recall: Set α := α → Prop
-- So if we have a set `s : Set α`, it is a function `s : α → Prop`.

-- To ask `s ∈ s`, we are asking "Does s return True when input to itself?".
-- `s(s)`
-- Input expectation: `s` expects an argument of type `α`.
-- Input provided:    `s` has type `Set α` (which is `α → Prop`).

-- ERROR: Type Mismatch!
-- `α` is not the same as `α → Prop`.
-- A function cannot take ITSELF as an argument.
-- It works like a ladder:
-- Level 0: The People (Type α)
-- Level 1: The Barber (Set α) -> Takes People as input.
-- The Barber is NOT a Person. The Barber lives one level up!

-- 3. A Valid, Non-Contradictory Example (The Hierarchy in Action)
-- Instead of a Barber trying to shave Barbers...
-- Let's have a Club trying to accept Members.

-- Level 0: The Citizens (Nat)
-- Level 1: The Club (Set Nat)

def SafeClub : Set Nat := { n | n % 2 = 0 } -- The "Evens" Club

-- A Citizen can join the Club:
example : 0 ∈ SafeClub := by simp [SafeClub] -- Valid! 0 is a Nat.

-- The Club CANNOT join itself.
-- "Does the SafeClub contain the SafeClub?"
-- example : SafeClub ∈ SafeClub := ...
-- ERROR: Types don't match.
-- SafeClub expects a `Nat`. We gave it a `Set Nat`.
-- This prevents the paradox from ever starting!

-- 2. Let's force Lean to try the Paradox (Barber):

def Barber (α : Type) : Set (Set α) :=
  { x | x ∉ x }

-- ERROR expecting:
-- term `x` has type `Set α` but is expected to have type `α`
-- (Or similar universe/type checker error).
