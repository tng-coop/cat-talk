-- VISUALIZING CANTOR'S DIAGONAL ARGUMENT
-- User Question: "Both Nat and Nat->Bool are infinite. Why is one bigger?"

import Mathlib.Data.Nat.Basic

-- 1. THE SETUP
-- Assume we have a Nametag for every Function.
-- This means we have a SEQUENCE of functions: f_0, f_1, f_2 ...
-- Let's visualize their outputs as an infinite table of bits (0/1).

/-
      | 0 | 1 | 2 | 3 | ... (Inputs)
---------------------------
 f_0  | 1 | 0 | 1 | 0 | ...
 f_1  | 0 | 0 | 1 | 1 | ...
 f_2  | 1 | 1 | 1 | 0 | ...
 f_3  | 0 | 0 | 0 | 0 | ...
 ...
-/

-- 2. THE DIAGONAL
-- Look at the bits on the main diagonal:
-- f_0(0) = 1
-- f_1(1) = 0
-- f_2(2) = 1
-- f_3(3) = 0

-- 3. THE "ANTI-DIAGONAL" (The Barber)
-- Let's define a new function `D` that FLIPS the diagonal bit.
-- D(n) := ¬ f_n(n)

def AntiDiagonal (f : Nat → (Nat → Bool)) : (Nat → Bool) :=
  fun n => ! (f n n)

-- 4. THE CONTRADICTION
-- Does `D` have a nametag? Is `D` equal to some `f_k`?
-- Let's check index `k`:
-- D(k)   = ¬ f_k(k)   (By Definition of D)
-- f_k(k) = f_k(k)     (By Definition of f_k)

-- They differ at position `k`.
-- So `D` is NOT `f_k`.
-- This is true for ANY `k`.

-- 5. CONCLUSION
-- `D` is a valid function (Nat -> Bool).
-- But it is NOT in the list f_0, f_1, f_2...
-- Therefore, "The List" (Nat) cannot hold "All Functions" (Nat -> Bool).
-- The set of functions is a "Bigger Infinity".
