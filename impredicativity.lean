-- IMPREDICATIVITY DEMO
-- "Impredicativity" means defining something by referring to a collection that contains it.

-- 1. PROP is IMPREDICATIVE (Example: "Falsehood")
-- We define `MyFalse` by quantifying over ALL Propositions (`∀ p : Prop`).
-- Crucially, `MyFalse` ITSELF is a Proposition.
-- So we are using a collection (All Props) to define a member of that collection (MyFalse).
-- In restricted systems, this is circular. In Lean's Prop, it is allowed.

def MyFalse : Prop := ∀ (p : Prop), p

#check MyFalse -- Output: MyFalse : Prop (It stayed at Level 0!)


-- 2. TYPE is PREDICATIVE (Example: "Polymorphic Identity")
-- Let's try to define a Type that refers to ALL Types.
-- `MyType` tries to be the type of function that takes ANY type and returns it.

def MyType : Type 1 := ∀ (α : Type), α

#check MyType -- Output: MyType : Type 1

-- Why Type 1?
-- Because to quantify over "All Types", you must stand ABOVE them.
-- You cannot define a `Type 0` by looking at all `Type 0`s.
-- This "Universe Bumping" is what prevents the Barber Paradox for logical data.

-- 3. THE NAIVE MISTAKE
-- Early (Naive) Set Theory assumed you could do what `Prop` does, but for `Sets`.
-- They thought: Set = { x | P(x) } where P quantifies over everything.
-- That collapsed the universe.
