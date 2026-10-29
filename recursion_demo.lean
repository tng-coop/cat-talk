/-
  Nuts and Bolts of Recursion: Structure vs Inductive
-/

-- 1. Why Structures FAIL at recursion
-- A Structure is a "Product Type" (AND).
-- To build 'RecursiveStruct', you need ALL parts at the same moment.
-- Parts: (data : Int) AND (next : RecursiveStruct)
-- To build 'next', you need ANOTHER (data AND next')...
-- It never ends. It's an infinite loop just to create ONE item.

-- class RecursiveStruct where
--   data : Int
--   next : RecursiveStruct -- ERROR: Infinite size requried!


-- 2. Why Inductive Types SUCCEED
-- An Inductive Type is a "Sum Type" (OR).
-- To build 'RecursiveList', you pick ONE option.
-- Options: (End) OR (Data AND Next)
inductive RecursiveList where
  | end_of_list : RecursiveList                     -- STOP HERE. (The "Base Case")
  | node        : Int → RecursiveList → RecursiveList -- GO DEEPER.

-- Nuts and Bolts:
-- The "Constructor" (| end_of_list) gives us a way to *finish*.
-- A Structure has only one constructor (mk), which requires everything.
-- An Inductive type has multiple constructors, allowing us to choose the non-recursive path.

def works : RecursiveList :=
  RecursiveList.node 1 (RecursiveList.node 2 RecursiveList.end_of_list)
