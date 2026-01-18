
-- 1. STRUCTURE (Data)
-- Used for explicit data you pass around by hand.
structure Point where
  x : Int
  y : Int

-- 2. CLASS (Metadata)
-- Used for implicit data the computer finds for you.
-- NOTICED: The syntax is Identical!
class MyClassPoint where
  x : Int
  y : Int

-- 3. INSTANTIATION (Making one)

-- For Structure: We use `def`
def explicitPoint : Point := {
  x := 1
  y := 2
}

-- For Class: We use `instance`
-- But the body `{ ... }` is EXACTLY the same constructor!
instance : MyClassPoint := {
  x := 1
  y := 2
}
