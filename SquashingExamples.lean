
-- "Squashing" means the result stays small (Prop / Sort 0),
-- even if the input is HUGE (Type u).

universe u

-- EXAMPLE 1: NO SQUASH (The Balloon)
-- We make a List of items.
-- If the items are Big, the List is Big.
def MyList (α : Type u) : Type u := List α
#check MyList.{0} -- List Nat  : Type 0
#check MyList.{5} -- List ...  : Type 5
-- The container GROWS to fit the content.


-- EXAMPLE 2: SQUASH (The Black Hole)
-- We make a Statement about items.
-- "For all items x, x equals itself."
def MyStatement (α : Type u) : Prop := ∀ x : α, x = x

-- Logic doesn't care how big the items are.
#check MyStatement.{0} -- (∀ n:Nat, n=n) : Prop (Sort 0)
#check MyStatement.{5} -- (∀ x:Huge, x=x) : Prop (Sort 0)
-- The container STAYS SMALL (Prop) even if content is huge.


-- EXAMPLE 3: The "Quiver" Dial
-- v is the "Squash Dial".
variable (v : Level) -- (Pseudo-code for concept)

-- If v=1 (Type), we keep the data structure (List-like).
-- If v=0 (Prop), we squash it to a boolean (Connected?).
