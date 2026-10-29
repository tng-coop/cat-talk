-- IMAGINE this was allowed (It is currently BANNED by Strict Positivity)
-- inductive Barber
--   | mk : (Barber → Bool) → Barber

-- This type definition says:
-- "A Barber is an object that contains a 'Law'.
--  The Law takes a Barber as input, and returns Yes/No (Bool)."

-- We can define "Shaving" as:
-- "To check if Barber A shaves Barber B, we look at A's Law and apply it to B."
-- def shaves (a : Barber) (b : Barber) : Bool :=
--   match a with
--   | Barber.mk law => law b

-- NOW THE PARADOX:
-- Let's construct a "Village Barber" named `vb`.
-- His Law is: "I shave `x` IF AND ONLY IF `shaves x x` is False."

-- def villageBarberRule (x : Barber) : Bool :=
--   not (shaves x x)

-- def villageBarber : Barber :=
--   Barber.mk villageBarberRule

-- THE CRASH:
-- Does `villageBarber` shave `villageBarber`?
-- value = shaves villageBarber villageBarber
--       = villageBarberRule villageBarber
--       = not (shaves villageBarber villageBarber)
--       = not value

-- value = not value  (IMPOSSIBLE!)
-- True = False? False = True?
-- The universe explodes.
