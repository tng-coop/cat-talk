inductive Tree
  | mk : (Nat → Tree) → Tree

-- 1. Example: (Nat -> Tree) -> Tree
-- This is just the constructor!
def pack (f : Nat → Tree) : Tree :=
  Tree.mk f

-- 2. Example: Tree -> (Nat -> Tree)
-- This is just pattern matching ("unwrapping")
def unpack (t : Tree) : Nat → Tree :=
  match t with
  | Tree.mk f => f

-- Proof that they are perfect copies (Isomorphic)
example (f : Nat → Tree) : unpack (pack f) = f := rfl
example (t : Tree) : pack (unpack t) = t := by
  cases t
  rfl
