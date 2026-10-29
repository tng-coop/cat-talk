-- 1. "Polymorphic" Argument (Quantifying over Types)
-- (α : Type) means "For ANY Type α" (e.g., Nat, Bool, String)
example (α : Type) (x : α) : x = x := rfl

-- 2. Value Argument (Quantifying over Values)
-- (n : Nat) means "For ANY natural number n" (e.g., 0, 1, 2, 100...)
example (n : Nat) : n + 0 = n := rfl

-- 3. Specific Values
-- You usually don't pass specific values like '1' as generic arguments.
-- Instead, you write theorems ABOUT specific values.
example : 1 + 1 = 2 := rfl

abbrev MySet (α : Type) := α → Prop

-- 4. Dependent Types (The line blurs!)
-- Some Types DEPEND on values, like "Fin n" (Numbers less than n).
-- Here, 'n' is a value (like 2), but it shapes the Type.
example (n : Nat) (i : Fin n) : i.val < n := i.isLt

-- Concrete example with "1 or 2"
-- "Fin 2" is the type of numbers {0, 1} (size 2) (Wait, 0 and 1. Not 1 and 2.)
-- Let's stick to Nat for simplicity in this demo.
def oneOrTwo : MySet Nat := {1, 2}
