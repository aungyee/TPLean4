-- suppose we have an implementation of List as follows:
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs

#check Lst
#check Lst.cons
#check Lst.nil
#check Lst.append

-- then we can construct a list of Nat as follows:
#eval Lst.cons Nat 0 (Lst.nil Nat)
#eval Lst.append Nat (Lst.nil Nat) (Lst.cons Nat 3 (Lst.nil Nat))

-- alternatively, the type of the list can be inferred from the type of the elements
#eval Lst.cons _ 0 (Lst.nil _)
#eval Lst.append _ (Lst.nil _) (Lst.cons _ 3 (Lst.nil _))

/-
When a function takes an argument that can generally be inferred from context,
Lean allows you to specify that this argument should, by default, be left implicit.
This is done by putting the arguments in curly braces, as follows:
-/

def Lst2.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst2.nil {α : Type u} : Lst α := List.nil
def Lst2.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#eval Lst2.cons 0 Lst2.nil
#eval Lst2.append (Lst2.nil) (Lst2.cons 3 Lst2.nil)

-- All that has changed are the braces around α : Type u in the declaration of the variables.
-- We can also use this device in function definitions:

def ident {α : Type u} (x : α) := x

#check ident

-- Checking the type of ident requires wrapping it in parentheses to avoid having its signature shown:
#check (ident)
#check ident 1
#check ident "hello"

-- to make the implicit argument explicit
#check @ident
#check @ident Nat 1


-- variables can also be declared implicit
section
  variable {α : Type u}
  variable (x : α)
  def ident2 := x
end

#check ident2
#check ident2 4
#check ident2 "hello"

/-
?m.1 is a placeholder (a "metavariable") for a type Lean has not worked out yet.

List.nil and id have an implicit argument {α : Type u}. Lean fills it in from context,
e.g. in id 1, the 1 tells Lean that α = Nat.
Here there is no context, so Lean doesn't know α and shows ?m.1 instead:
  List.nil : List ?m.1      -- an empty list of some unknown type
  id       : ?m.1 → ?m.1    -- takes and returns a value of some unknown type
-/
#check (List.nil)
#check (id)

-- giving the type explicitly removes the placeholder
#check (List.nil : List Nat)
#check (id : Nat → Nat)

-- Numerals are overloaded in Lean, but when the type of a numeral cannot be inferred,
--  Lean assumes, by default, that it is a natural number.
#check 2
#check (2 : Nat)
#check (2 : Int)
