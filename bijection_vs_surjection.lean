import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

variable {α : Type}

-- 1. INJECTION IS EASY (One-to-One)
-- We CAN fit the "Small" (α) into the "Large" (Set α).
-- Mapping: Each person 'x' is mapped to the singleton club '{x}'.
def toSingleton (x : α) : Set α := {x}

theorem injection_exists : Function.Injective (toSingleton : α → Set α) := by
  -- Proof: If {a} = {b}, then a = b.
  intro a b h
  simp [toSingleton] at h
  exact h

-- 2. SURJECTION IS IMPOSSIBLE (Onto)
-- We CANNOT cover the "Large" (Set α) with the "Small" (α).
-- This is what Cantor's/Barber's argument proves.
theorem surjection_impossible : ¬ ∃ (f : α → Set α), Function.Surjective f := by
  intro hExists
  rcases hExists with ⟨f, hSurj⟩

  -- The Diagonal Set (The Barber)
  let Barber := { x | x ∉ f x }

  -- Because f is Surjective, SOME element 'b' must map to 'Barber'.
  rcases hSurj Barber with ⟨b, hb⟩

  -- Contradiction ensues.
  have h : b ∈ Barber ↔ b ∉ Barber := by
    rw [← hb]
    simp [Barber]
  simp at h

-- CONCLUSION:
-- We have Injection (Small fits in Large).
-- We lack Surjection (Large does NOT fit in Small).
-- Therefore, we lack Bijection (Sizes are strictly different).
