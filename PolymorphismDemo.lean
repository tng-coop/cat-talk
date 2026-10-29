import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Nat.Basic

open CategoryTheory

-- ==========================================
-- 1. THE "OPEN FOR BUSINESS" SIGN (Polymorphism)
-- ==========================================

-- This function "is_connected" works for ANY type V
-- that has a [Quiver V] instance.
def is_connected {V : Type} [Quiver V] (a b : V) : Prop :=
  Nonempty (a ⟶ b)


-- ==========================================
-- 2. THE CUSTOMERS (Concrete Instances)
-- ==========================================

-- Customer A: The Order Category
-- We use a Structure to make a completely new Type "OrderW"
structure OrderW where val : Nat
instance : OfNat OrderW n := ⟨{val := n}⟩

instance : Quiver OrderW where
  Hom a b := PLift (a.val ≤ b.val)

instance : CategoryStruct OrderW where
  id a := PLift.up (Nat.le_refl a.val)
  comp f g := PLift.up (Nat.le_trans f.down g.down)


-- Customer B: The Divisibility Category
-- A different Structure "DivW" for the same data
structure DivW where val : Nat
instance : OfNat DivW n := ⟨{val := n}⟩

instance : Quiver DivW where
  Hom a b := PLift (a.val ∣ b.val)

instance : CategoryStruct DivW where
  id a := PLift.up (Nat.dvd_refl a.val)
  comp f g := PLift.up (Nat.dvd_trans f.down g.down)


-- ==========================================
-- 3. THE TRANSACTION (Instantiation)
-- ==========================================

-- The polymorphic function accepts OrderW
-- We prove 3 <= 5
example : is_connected (3 : OrderW) 5 :=
  ⟨PLift.up (Nat.le_of_ble_eq_true rfl)⟩

-- The SAME polymorphic function accepts DivW
-- We prove 3 | 6
example : is_connected (3 : DivW) 6 :=
  ⟨PLift.up (Nat.dvd_of_mod_eq_zero rfl)⟩

-- But it fails for DivW if relation doesn't hold (3 | 5)
-- example : is_connected (3 : DivW) 5 := sorry -- Impossible

-- And it REJECTS plain Nat (Shop Closed)
-- #check is_connected (3 : Nat) 5 -- Error: failed to synthesize instance 'Quiver Nat'
