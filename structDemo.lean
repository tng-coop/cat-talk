structure abc where
  abc : Nat := 4

-- MAGIC TRICK: Turn the struct 'abc' into a class manually!
-- Must be done BEFORE we use it as a class in 'f' or 'instance'
attribute [class] abc

class dotcom where
  abc : Nat

#check ({ abc := 1 } : abc)
#check ({ abc := 1 } : dotcom)

#check abc

-- 1. Create an instance using the 'instance' keyword
instance : dotcom where
  abc := 42

-- To use the default value (4), we just leave the body empty!
instance : abc where
  -- abc := 42 -- Commented out to use the default value of 4

-- The syntax [x : abc] names the instance 'x' so we can use it.
def f [x : abc] : Nat := x.abc

#eval f -- Result: 4

-- 2. Now Lean can find it automatically!
#check inferInstanceAs dotcom
-- #eval (inferInstanceAs dotcom).abc -- result: 42

-- #check inst -- Error: unknown identifier 'inst'

-- If you want to use the name, you must give it one:
instance myParsableName : abc where
  abc := 99

#check myParsableName -- This works!

-- (Moved attribute [class] abc to top of file)

-- Now this works because 'abc` is officially a class:
#check inferInstanceAs abc

-- WHO USES THIS?
-- Everyone who wants one function to work on many types.

-- This function asks Lean: "Find me the 'Add' instance for 'MyType'!"
def double {MyType : Type} [Add MyType] (x : MyType) : MyType :=
  x + x

#eval double 10     -- Lean finds the instance for Nat automatically
#eval double 3.14   -- Lean finds the instance for Float automatically
