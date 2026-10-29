-- 1. ZERO WORK (Constant Constructors)
-- These take 0 arguments. You just "pick them up".

-- TRUE: The classic example.
#check True.intro
-- Values: Just one. "trivial".

-- UNIT: The "Data" version of True.
#check Unit.unit
-- Values: Just one. "()".

-- MY OWN ENUM:
inductive TrafficLight
  | red    -- 0 args
  | yellow -- 0 args
  | green  -- 0 args

-- 2. SOME WORK (Argument Constructors)
-- You cannot just "have" these. You must "build" them from parts.

-- AND: Needs 2 things.
#check And.intro
-- You need to provide (left_proof) and (right_proof).

-- OR: Needs 1 thing.
#check Or.inl
-- You need to provide (left_proof).

-- 3. HIDDEN WORK (Implicit Arguments)
-- `rfl` looks like a constant, but it's cheating.
-- It secretly grabs the value from the context.
#check rfl
-- It constructs `Eq.refl a`. It needs `a`.

-- 4. MOST WORK (Functions)
-- A proof of `A -> B` is a machine that DOES work.
