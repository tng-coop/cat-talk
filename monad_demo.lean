import Mathlib

open CategoryTheory

/-!
# Inspecting Mathlib's Monad Components for List

We use `ofTypeMonad` to convert the standard Lean `List` Monad into a `CategoryTheory.Monad`.
-/

-- 1. Grab the Category Theory Monad instance for List
noncomputable def ListCatMonad : CategoryTheory.Monad Type := CategoryTheory.ofTypeMonad List

-- 2. Extract η (Eta)
noncomputable def realEta := ListCatMonad.η

/-!
### What is η?
It is the "Unit" of the Monad.
In `CategoryTheory.Monad.Types`, it is defined as wrapping `pure`.
-/
-- Check the type: It takes a value of type α and returns a List α.
#check realEta.app Nat -- Nat → List Nat


-- 3. Extract μ (Mu)
noncomputable def realMu := ListCatMonad.μ

/-!
### What is μ?
It is the "Multiplication" of the Monad.
In `CategoryTheory.Monad.Types`, it is defined as wrapping `join` (or atomic bind).
-/
-- Check the type: It takes a List of Lists and returns a List.
#check realMu.app Nat -- List (List Nat) → List Nat
