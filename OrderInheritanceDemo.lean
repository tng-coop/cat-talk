
-- 1. These are "Mixins" or "Tags"
-- `LE α` just means "This type has a symbol `≤` defined."
-- `LT α` just means "This type has a symbol `<` defined."

class LE_Demo (α : Type) where
  le : α → α → Prop

class LT_Demo (α : Type) where
  lt : α → α → Prop


-- 2. `extends` combines them
-- When Preorder extends them, it says:
-- "To be a Preorder, you MUST already have `≤` and `<` defined (or define them right now)."
-- It bundles the symbols together with the PROOFS.

class Preorder_Demo (α : Type) extends LE_Demo α, LT_Demo α where
  -- Now we add the RULES (Axioms)
  le_refl : ∀ a : α, le a a
  le_trans : ∀ a b c : α, le a b → le b c → le a c
  -- We also enforce a connection between < and <=
  lt_iff_le_not_le : ∀ a b : α, lt a b ↔ (le a b ∧ ¬ le b a)


-- 3. Making an Instance
-- You provide the symbols First, then the proofs.

instance : Preorder_Demo Nat where
  le a b := a ≤ b
  lt a b := a < b
  le_refl := Nat.le_refl
  le_trans := Nat.le_trans
  lt_iff_le_not_le := sorry -- (Skipped proof for demo)
