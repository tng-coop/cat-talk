inductive StringTree
  | mk : (String → StringTree) → StringTree

-- Proof it works: simpler than Nat
def myNode : StringTree :=
  StringTree.mk (fun s =>
    if s == "left" then myNode -- infinite recursion logic
    else myNode
  )
