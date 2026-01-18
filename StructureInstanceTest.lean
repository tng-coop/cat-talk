
structure MyDataStruct where
  x : Int

-- 1. Can we use `instance` on a raw structure?
-- The expectation: "failed to synthesize" or "not a class" error,
-- OR it works but simply registers it harmlessly.
instance : MyDataStruct where
  x := 10

-- 2. Can we find it?
-- If the above worked, does inference work?
def findIt [d : MyDataStruct] : Int := d.x

-- This will fail if MyDataStruct is not a class.
#check findIt
