-- "What does change do?"
-- A simple playground to see it in action.

example : 1 + 1 = 2 := by
  -- Initial Goal: ⊢ 1 + 1 = 2

  -- We can "change" the view to anything EQUIVALENT.
  change 2 = 2
  -- Lean checks: Is (1+1) equal to (2)? Yes.
  -- It updates the goal. Now: ⊢ 2 = 2

  rfl

example : 1 + 1 = 2 := by
  -- We can even change it to something "more complex" but equivalent
  change (0 + 1) + 1 = 2

  -- Or back to the original
  change 1 + 1 = 2

  rfl
