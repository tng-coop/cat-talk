
-- 1. 5 : Int?
#check 5

-- 2. Int -> Prop : Prop?
-- User hypothesis: The type of functions from Int to Prop is itself a Prop.
-- My hypothesis: It is a Type (specifically Type 0).
#check Int → Prop

-- 3. A specific function f
variable (f : Int → Prop)
#check f -- f : Int → Prop

-- 4. Result of application
variable (x : Int)
#check f x -- f x : Prop
