/-
function definition using def
-/

def double (n : Nat) : Nat := n + n

-- invoking the function
#eval double 2

-- alternative way of defining the same function
def double2 : Nat → Nat := fun n => n + n

#eval double2 2

-- or infer the type completely
def double3 := fun (n : Nat) => n + n

#eval double3 2

/-
the general form of a function definition is as follows:

    def foo : α := bar

where α is the type of the expression bar. α can be inferred and can be omitted.
-/

-- the expression bar can be anything so it can be used to define a value like we've seen
def pi : Float := 3.1415


-- def can take multiple arguments
def add (x y : Nat) : Nat := x + y
#eval add (double 1) 2

-- arguments can be separated
def add2 (x : Nat) (y : Nat) : Nat := x + y
#eval add2 (double 1) 2

-- more interesting expression can be used for bar
def greater (x y : Nat) := if x > y then x else y
#eval greater 10 5

-- functions can be defined in terms of other functions
def doTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
#eval doTwice double 2

-- more generally/abstractly
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=g (f x)
#eval compose Nat Nat Nat double double 2


/- Reduction to definitions -/
def Natural := Nat
example : Natural = Nat := rfl

-- but the following does not work
def five : Natural := 5

/-
Why one works and the other doesn't:

"Unfolding" a name means replacing it with its definition (Natural becomes Nat).
A name made with def is "semireducible", meaning Lean unfolds it only sometimes:

- rfl: Lean unfolds Natural to Nat, sees Nat = Nat, so the proof works.
- def five : Natural := 5
  To accept 5 as a Natural, Lean looks for a rule saying "numbers can be Naturals".
  It does NOT unfold Natural while looking. A rule exists for Nat, but none for Natural,
  so it fails.
-/
