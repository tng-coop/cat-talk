import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

variable {α : Type}

-- "The Barber Paradox (Russell's Paradox)" logic was:
-- Barber = { x | x ∉ x }
-- And asking if Barber ∈ Barber led to a contradiction.

-- "Cantor's Theorem" (1891) uses the EXACT SAME logic properly:
-- D = { x | x ∉ f x }
-- And asks if D is in the "image" of f.

theorem cantor (f : α → Set α) : ¬ Function.Surjective f := by
  -- 1. Assume there IS a surjection 'f'
  -- (i.e., Assume there is a Barber who shaves EVERYONE in the target list)
  intro h

  -- 2. Construct the "Diagonal Set" (The Barber Set)
  -- "The set of all elements x that are NOT in the set assigned to them by f"
  let D := { x | x ∉ f x }

  -- 3. Since 'f' is surjective, there must be some 'a' such that f(a) = D.
  -- (Thinking: "There must be a citizen 'a' whose assigned list is exactly the Diagonal list")
  rcases h D with ⟨a, ha⟩

  -- 4. Now we ask: Is 'a' in D?
  -- (Thinking: "Does the Barber 'a' shave himself?")

  -- Logic: a ∈ D <-> a ∉ f a
  -- But f a = D, so: a ∈ D <-> a ∉ D
  have self_ref_contradiction : a ∈ D ↔ a ∉ D := by
    rw [← ha] -- Replace D with (f a) in the right side
    simp [D]  -- Unfold the definition of D: "x ∈ D" means "x ∉ f x"

  -- 5. Contradiction! (p <-> not p) is impossible.
  simp at self_ref_contradiction

-- CONCLUSION:
-- The logic that BREAKS Set Theory (if applied to the Universe)
-- Is the logic that PROVES there are differnet sizes of Infinity (when applied to Power Sets).
-- |Set Nat| > |Nat|
