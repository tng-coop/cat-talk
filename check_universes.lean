class Catnip(t:Type u) where
  Obj : t

instance i_type : Catnip Type where
  Obj := Nat

instance i_nat : Catnip Nat where
  Obj := 1

set_option pp.universes true
#check @i_type
#check @i_nat
