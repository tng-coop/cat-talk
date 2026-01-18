
-- 1. Define a new type.
inductive RockPaperScissors
| rock
| paper
| scissors

-- 2. At this point, writing `rock ≤ paper` is an ERROR.
-- "failed to synthesize instance LE RockPaperScissors"

-- 3. We INSTANTIATE the class LE for our type.
instance : LE RockPaperScissors where
  le a b :=
    match a, b with
    -- Rock matches Rock (Reflexive)
    | .rock, .rock => True
    -- Rock loses to Paper (Rock ≤ Paper)
    | .rock, .paper => True
    -- Paper beats Rock, so Paper is "Greater" (Not ≤)
    | .paper, .rock => False
    -- ... (fill in the rest) ...
    | _, _ => True -- lazy default

-- 4. NOW the notation works!
#check RockPaperScissors.rock ≤ RockPaperScissors.paper
-- Result: Prop
