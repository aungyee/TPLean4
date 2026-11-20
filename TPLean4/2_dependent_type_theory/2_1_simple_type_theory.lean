/- Define some constants. -/

def m : Nat := 1       -- m is a natural number (a Lean natural number is an arbitrary-precision unsigned integer)
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false


/- Check their types. -/

#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1

-- "&&" is the Boolean and
#check b1 && b2

-- Boolean or
#check b1 || b2

-- Boolean "true"
#check true

/- Evaluate -/

#eval 5 * 4
#eval m + 2
#eval b1 && b2


/- Building new types out of existing types -/

-- function from Nat to Nat
#check Nat → Nat

-- product
#check Nat × Nat
#check Prod Nat Nat

-- function type is right-associative
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)

-- product type is not associative
#check Nat × Nat → Nat
#check Nat × (Nat → Nat)

-- functional (a mapping from a vector space of functions into its underlying scalar field)
#check (Nat → Nat) → Nat


/- other examples -/

-- function evaluation is f x instead of f(x) like other languages
#check Nat.succ
#check Nat.succ 0
#eval Nat.succ 0

-- we can think of Nat.add is a function that takes a Nat and returns a function that takes a Nat and returns a Nat
#check Nat.add
#check Nat.add 1
#check Nat.add 1 2
#eval Nat.add 1 2

-- component extraction of pairs
#check (0,1.1)
#check (0,1.1).fst
#check (0,1.1).1
#eval (0,1.1).fst
#check (0,1.1).snd
#check (0,1.1).2
#eval (0,1.1).snd
