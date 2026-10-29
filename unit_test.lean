-- The User's Hypothesis:
-- "If I replace Bool with Unit, the cardinality is 1 (safe). Does Lean allow it?"

inductive UnitWrapper
  | mk : (UnitWrapper → Unit) → UnitWrapper

-- UNCOMMENTING THE ABOVE:
-- Expectations:
-- Logically: Safe (Isomorphic to UnitWrapper).
-- Syntactically: Banned ("non-positive occurrence").
