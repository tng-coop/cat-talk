
-- 1. Without `*` (Defaults to Type 0)
class MyClassFixed (α : Type) where
  val : α

#check MyClassFixed
-- MyClassFixed : Type → Type


-- 2. With `*` (Polymorphic)
-- `Type*` tells Lean to allow α to be in ANY universe level.
-- It is equivalent to `{u : Level} (α : Type u)`
class MyClassPoly (α : Type*) where
  val : α

#check MyClassPoly
-- MyClassPoly.{u} (α : Type u) : Type u
