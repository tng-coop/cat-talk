import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.Tactic.ToDual

universe v u
open CategoryTheory

-- 1. SETUP: We need a CategoryStruct to have an 'Identity' (𝟙)
variable {V : Type u} [CategoryStruct.{v} V]

-- 2. A Real Definition: "IsIdentity"
-- "f is an identity if f equals the Identity Morphism of that object"
def IsIdentity {a : V} (f : a ⟶ a) : Prop := f = 𝟙 a

-- We register it for dualization.
attribute [to_dual self] IsIdentity

-- 3. A Real Theorem: "The Opposite of Identity is Identity"
-- If f is the identity on 'a', then f.op is the identity on 'op a'.
@[to_dual is_identity_op]
theorem identity_preservation {a : V} (f : a ⟶ a) (h : IsIdentity f) : IsIdentity (Quiver.Hom.op f) := by
  -- Proof:
  -- h says: f = 𝟙 a
  -- We want: f.op = 𝟙 (op a)

  -- Logic:
  -- The dual of `𝟙 a` is defined as `𝟙 (op a)`.
  -- So if f = 1, then f.op = 1.op = 1.

  dsimp [IsIdentity] at *
  rw [h]
  simp

-- 4. Verify Types
#check @identity_preservation
#check @is_identity_op

-- 5. Loop Definition
-- A Loop is just an arrow from an object to itself.
def Loop (a : V) := a ⟶ a

-- Register for dualization
attribute [to_dual self] Loop

-- 6. Loop Theorem
-- "The Dual of a Loop is a Loop"
-- If f is a loop on a, then f.op is a loop on op a.
@[to_dual loop_op_is_loop]
def loop_dual {a : V} (f : Loop a) : Loop (Opposite.op a) := f.op

-- 7. Verify Types
#check @loop_dual
#check @loop_op_is_loop
