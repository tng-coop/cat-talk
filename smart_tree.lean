inductive LazyTree
  | leaf : LazyTree
  | node : (Nat → LazyTree) → LazyTree

-- A Tree where the structure DEPENDS on `i`
def smartTree : LazyTree :=
  LazyTree.node (fun i =>
    if i == 0 then LazyTree.leaf       -- Child 0 is dead end
    else if i == 1 then smartTree      -- Child 1 loops back (infinite depth)
    else LazyTree.leaf                 -- All other children are dead ends
  )

-- How logical access works
def checkChild (t : LazyTree) (idx : Nat) : String :=
  match t with
  | LazyTree.leaf => "It is a leaf"
  | LazyTree.node f =>
      -- We feed `idx` into the stored function `f`
      match f idx with
      | LazyTree.leaf => "Variable Branch " ++ toString idx ++ " led to leaf"
      | LazyTree.node _ => "Variable Branch " ++ toString idx ++ " goes deeper"
