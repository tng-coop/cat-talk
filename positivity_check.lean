inductive AllowedTree
  | node : (Nat → AllowedTree) → AllowedTree

-- This one should fail
inductive Banned
  | mk : (Banned → Nat) → Banned
