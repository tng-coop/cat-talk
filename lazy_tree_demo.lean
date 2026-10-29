inductive LazyTree
  | node : (Nat → LazyTree) → LazyTree

-- 1. CONSTRUCTION: How to build one?
-- You provide a "Recipe" (Function).
-- This tree is infinite: At index `n`, it puts a new node.
-- (This creates a tree that just branches forever)
def universalTree : LazyTree :=
  LazyTree.node (fun n => universalTree)
  -- Note: "n" is ignored here, every child is the same infinite tree.

-- A more interesting tree:
-- Each branch "remembers" its path index.
partial def pathTree (depth : Nat) : LazyTree :=
  LazyTree.node (fun branchIndex => pathTree (depth * 10 + branchIndex))

-- 2. DESTRUCTION: How to read it?
-- You "apply" the node to a number.
def getChild (t : LazyTree) (n : Nat) : LazyTree :=
  match t with
  | LazyTree.node childFunc => childFunc n

-- 3. USAGE
-- Let's navigate the pathTree!
-- Root -> Child 5 -> Child 2 -> Child 1
-- (Should represent number 521 conceptually)
def specificNode : LazyTree :=
  let root := pathTree 0
  let step1 := getChild root 5
  let step2 := getChild step1 2
  let step3 := getChild step2 1
  step3

-- Note: In Lean, this is PURELY LOGICAL/FUNCTIONAL.
-- No infinite memory is allocated. Memory is only allocated when you call `getChild`.
