class Catnip(Obj:Type u) where
  Arr : Obj -> Obj -> Sort v

instance : Catnip Type where
  Arr a b := a->b

instance : Catnip Nat where
  Arr a b := a <= b

open Catnip

#check (Arr 1 1)
example : (Arr 1 1) = (1 <= 1) := rfl
example: Nat := 45
