structure Person where
  name : String

-- The "Relation" on the set of People.
-- (shaves a b) means "Person a shaves Person b"
def ShavesRelation := Person → Person → Prop

-- The Famous Condition
def is_paradox_barber (b : Person) (shaves : ShavesRelation) : Prop :=
  -- For every person p in the village:
  ∀ p : Person,
    -- The Barber shaves p  <==>  p does NOT shave p
    shaves b p ↔ ¬(shaves p p)

-- The Proof of Impossibility
theorem no_such_barber_exists
  (shaves : ShavesRelation) :
  ¬(∃ b : Person, is_paradox_barber b shaves) :=
  by
  intro hExists
  obtain ⟨b, hRule⟩ := hExists
  -- Let's see what the rule says about 'b' himself:
  have hSelf := hRule b
  -- hSelf : shaves b b ↔ ¬shaves b b
  -- Now we have (P <-> Not P), which is a contradiction.
  have hContradiction : False := iff_not_self hSelf
  exact hContradiction
