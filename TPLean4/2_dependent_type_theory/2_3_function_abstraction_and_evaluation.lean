/-
Lean provides a fun (or λ) keyword to create a function from an expression as follows:
-/

#check fun (x : Nat) => x + 1
#check λ (x : Nat) => x + 1
example : (fun (x : Nat) => x + 1) = (λ (x : Nat) => x + 1) := rfl

-- the type of the argument can be inferred
#check fun x => x + 1

-- evaluation
#eval (λ x => x + 1) 2

/-
more examples
-/

-- the following are the same
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0
def n : Nat := 0

-- identity function
#check fun x : Nat => x

-- constant function that ignores its argument
#check fun _x : Nat => true

-- composition of functions
#check fun x : Nat => g (f x)
#check fun x => g (f x)

-- function as parameters
#check fun (a : String → Bool) (b : Nat → String) (c : Nat) => a (b c)

-- type as parameters
#check fun (α β γ : Type) (a : β → γ) (b : α → β) (c : α) => a (b c)

-- the parameters are bound variables waiting to be instantiated
-- applying a term t : α → β to a term s : α yields an expression t s : β
#check (fun x : Nat => x) 1
#check (fun _x : Nat => true) 1
#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0

/-
Two terms that reduce to the same value are called definitionally equal.
They are considered “the same” by Lean's type checker,
and Lean does its best to recognize and support these identifications.
-/
