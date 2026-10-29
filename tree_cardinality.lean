inductive MyTree
  | leaf : MyTree
  | branch : (Nat → MyTree) → MyTree

-- A simple function that builds an infinite tree
def infiniteBranch : MyTree :=
  MyTree.branch (fun _ => MyTree.leaf)
