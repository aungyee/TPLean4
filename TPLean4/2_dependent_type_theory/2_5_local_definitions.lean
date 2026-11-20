/-
Lean also allows you to introduce “local” definitions using the let keyword.
The expression let a := t1; t2 is definitionally equal to the result of
replacing every occurrence of a in t2 by t1.
-/

-- definitionally equal to (2 + 2) * (2 + 2)
#check let y := 2 + 2; y * y
#eval let y := 2 + 2; y * y
example : let y := 2 + 2; y * y = (2 + 2) * (2 + 2) := rfl

-- definitionally equal to (2 + 2) + 3
#check let y := 2 + 2; y + 3
#eval  let y := 2 + 2; y + 3
example : let y := 2 + 2; y + 3 = (2 + 2) + 3 := rfl

-- definitionally equal to 3
#check let _y := 2 + 2; 3
#eval  let _y := 2 + 2; 3
example : let _y := 2 + 2; 3 = 3 := rfl

-- twice_double x is definitionally equal to the term (x + x) * (x + x).
def twice_double (x : Nat) : Nat := let y := x + x; y * y
#eval twice_double 2
example (x : Nat) : twice_double x = (x + x) * (x + x) := rfl

/-
Chaining multiple let-expressions
-/

-- definitionally equal to:
--   z * z
--   = (y + y) * (y + y)
--   = ((2 + 2) + (2 + 2)) * ((2 + 2) + (2 + 2))
#check let y := 2 + 2; let z := y + y; z * z
#eval  let y := 2 + 2; let z := y + y; z * z
example : let y := 2 + 2; let z := y + y; z * z = ((2 + 2) + (2 + 2)) * ((2 + 2) + (2 + 2)) := rfl

-- semicolons (;) can be omitted when line breaks are used
def t (x : Nat) : Nat :=
  let y := x + x
  y * y

#eval t 2

/-
let vs fun: they look similar, but are not the same.

  let a := t1; t2     -- a is a nickname for t1. Lean knows a = t1 while checking t2.
  (fun a => t2) t1    -- a is an unknown input. Lean checks t2 first, WITHOUT knowing a = t1.

Example: foo works, bar fails.

- foo: let a := Nat
  Lean knows a is Nat, so x : a means x : Nat, and x + 2 makes sense.

- bar: (fun a => fun x : a => x + 2) Nat
  Lean checks the function on its own first. Here a could be any type
  (Bool, String, ...), and you can't add 2 to a value of an unknown type.
  So it fails, even though Nat is passed in afterwards.
-/

def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
