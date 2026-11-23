set_option linter.unusedVariables false

variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
def t1_fun : Type → Type → Type := fun x => fun y => x -- this has the same form as t1
def t1_prop : Prop → Prop → Prop := fun x => fun y => x -- this has the same form as t1

-- check the type of t1 and t1_fun
#check type_of% @t1
#check type_of% @t1_fun

-- the types of p → q → p, Type → Type → Type, and Prop → Prop → Prop are different
#check p → q → p
#check Type → Type → Type
#check Prop → Prop → Prop

-- the type of theorems must be Prop
theorem t1_fun' : Type → Type → Type := fun x => fun y => x
theorem t1_prop' : Prop → Prop → Prop := fun x => fun y => x

-- use #print to see the proof of a theorem
#print t1

-- use show to state the expected type of an expression explicitly
theorem t1' : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp


-- like def, we can move the arguments to the left of the colon
theorem t1'' (hp : p) (hq : q) : p := hp
#print t1''

-- we can use theorem just like a function
axiom hp : p
theorem t2 : p → q := t1 hp

-- we can move all the arguments to the right of the colon
theorem t1''' : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp

-- with explicit (p q : Prop), we can pass in the propositions we want for p and q
-- e.g. t1'''' (p → q) (q → p) : (p → q) → (q → p) → (p → q)
theorem t1'''' (p q : Prop) (hp : p) (hq : q) : p := hp

#check t1'''' p q
#check t1'''' (p → q) (q → p)

-- composition of propositions
variable (p q r s : Prop)

theorem t2' (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
