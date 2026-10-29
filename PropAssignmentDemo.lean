-- WHAT DOES IT MEAN TO ASSIGN A TYPE TO A TERM?

-- 1. In Programming (Data):
-- "val : Int" means "val is a compiled integer".
def myNumber : Nat := 42
-- Meaning: "I have a number 42."

-- 2. In Logic (Propositions):
-- "proof : True" means "proof is a compiled verification of True".
def myProof : True := trivial
-- Meaning: "I have a verification object (trivial)."

-- 3. THE ACT OF ASSIGNMENT IS THE "CHECK"
-- When you write `def x : T := y`, you are asking the compiler:
-- "Does 'y' fit into the box labeled 'T'?"

-- Case A: Success
def success : 1 = 1 := rfl
-- Compiler: "Yes. `rfl` is a valid method to construct `1=1`."
-- Meaning: You have PROVEN 1=1.

-- Case B: Failure
-- def failure : 1 = 2 := rfl
-- Compiler: "No. `rfl` constructs `a=a`, but you asked for `1=2`."
-- Meaning: You FAILED to prove 1=2.

-- 4. SO WHAT IS "True"?
-- `True` is the "Free Parking" of logic.
-- The box exists. It has a ball in it (`trivial`).
-- Assigning it just means "I acknowledge this code block was reached."

-- Sometimes we use it to discard information:
def ignore_evidence (n : Nat) : True := trivial
-- "Give me any number, and I will give you back... nothing (just True)."
