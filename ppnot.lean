import Paperproof
variable (P : Prop)
theorem aaa : (P → False) = (P → P → False) := by
  apply propext -- logical equivalence implies equality for Prop
  constructor
  -- Direction 1: (P -> False) -> (P -> P -> False)
  -- "If P kills you, then P (and another P) kills you."
  . intro h p _
    exact h p

  -- Direction 2: (P -> P -> False) -> (P -> False)
  -- "If two doses of P kill you, one dose kills you (because you can reuse it)."
  . intro h p
    exact h p p

theorem test (p q : Prop) : p ∧ q → p := by
  intro h
  cases h with
  | intro hp hq => exact hp
