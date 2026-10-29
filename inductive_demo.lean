-- INDUCTIVE vs IMPREDICATIVE RECURSION

-- 1. VALID: Inductive Data (Constructive)
-- This is "Predicative" because we build it up in stages.
-- Stage 0: `nil`
-- Stage 1: `cons 1 nil`
-- Stage 2: `cons 2 (cons 1 nil)`
-- We never refer to "The set of all lists" to define a list.

inductive MyList (α : Type)
  | nil : MyList α
  | cons : α → MyList α → MyList α

-- 2. INVALID: The "Barber" in Data (Negative Recursion)
-- Remember the Barber Paradox: `x` taking `x` as input.
-- Or sets containing functions of themselves.
-- Let's try to define a Type that holds a Predicate of itself.

-- inductive BadType
--   | mk : (BadType → Prop) → BadType

-- UNCOMMENTING THE ABOVE CAUSES:
-- "arg #1 of 'BadType.mk' has a non-positive occurrence of the datatypes being declared"

-- WHY?
-- If `BadType` contains a function `BadType → Prop`,
-- then to build a `BadType`, you need to handle `BadType`s.
-- But `BadType` hasn't been built yet!
-- It's a vicious circle.

-- Unlike `List`, which wraps a *smaller* List,
-- This wraps a *Function* that can eat ANY `BadType`.
-- This is exactly the structure `Set A := A → Prop` used for the paradox.
