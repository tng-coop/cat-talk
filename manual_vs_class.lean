structure MyPlusStruct (α : Type) where
  add : α -> α -> α

-- Usage with Structure (Manual Passing)
def manualAdd (s : MyPlusStruct Nat) (x y : Nat) : Nat :=
  s.add x y

-- We have to manually build the "struct" of operations every time
def myNatPlus : MyPlusStruct Nat := { add := Nat.add }

#eval manualAdd myNatPlus 5 3    -- 8

--------- VS CLASS ---------

class MyPlusClass (α : Type) where
  add : α -> α -> α

-- Usage with Class (Automatic Finding)
-- The [ ] tells Lean: "Go look in your database for this!"
def autoAdd {α : Type} [c : MyPlusClass α] (x y : α) : α :=
  c.add x y

-- We register the instance once
instance : MyPlusClass Nat where
  add := Nat.add

#eval autoAdd 5 3                -- 8 (No 'myNatPlus' needed!)
