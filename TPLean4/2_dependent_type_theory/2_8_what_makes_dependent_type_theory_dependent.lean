/-
The short explanation is that types can depend on parameters.

You have already seen a nice example of this:

    the type of List α depends on the argument α

This dependence is what distinguishes List Nat and List Bool.

For another example,

    the type Vector α n, the type of vectors of elements of α of length n.

This distinguishes Vector Nat 0, Vector Float 0, Vector Nat 2, etc.
-/

-- the type of cons depends on the type of the list
def cons (α : Type) (a : α) (as : List α) : List α := List.cons a as

#check cons Nat 0 []
#check cons Bool
#check cons

/-
cons is a dependent function: the type of its output depends on its input.

Normal function:    Nat → Bool          -- output is always Bool
Dependent function: (a : α) → β a       -- output type β a changes with the input a

  α : Type        the type of the inputs
  β : α → Type    gives one type for each input ("family of types")
  (a : α)         names the input a, so the output type can mention it

Example: cons : (α : Type) → α → List α → List α
  cons Nat  : Nat → List Nat → List Nat
  cons Bool : Bool → List Bool → List Bool
  Different input type, different output type.
-/

-- some dependent functions definitions in the List namespace
#check @List.cons
#check @List.nil
#check @List.length
#check @List.append


/-
Dependent pair (Sigma type): a pair ⟨a, b⟩ where the TYPE of b depends on the VALUE of a.

  Normal pair:    α × β           b always has type β
  Dependent pair: (a : α) × β a   b has type β a, which changes with a
                  Σ a : α, β a    same type, another notation

Examples:

  Normal pair, Nat × Bool: the second part is always a Bool
    (1, true)
    (2, false)

  Dependent pair, Σ a : Type, a: the second part's type IS the first part
    ⟨Nat, 5⟩          5 is a Nat
    ⟨Bool, true⟩      true is a Bool
    ⟨String, "hi"⟩    "hi" is a String

  Dependent pair, Σ a : Type, List a: the second part is a list of the first part
    ⟨Nat, [1, 2, 3]⟩
    ⟨Bool, [true, false]⟩

f and g: both build the pair ⟨a, b⟩, one with each notation.
  ⟨a, b⟩ is shorthand for Sigma.mk a b.

h1 and h2: call f with
  α := Type          the first part is a type
  β := fun α => α    the second part's type is the first part itself
  a := Nat           so the second part must be a Nat
  b := x             x : Nat fits

  h1 x  returns the whole pair ⟨Nat, x⟩, of type Σ a : Type, a
  h2 x  returns only the second part (.2), which is x, so h2 5 = 5
-/

universe u v

-- construct a dependent pair <a, b>
def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a := ⟨a, b⟩
def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a := Sigma.mk a b

-- build a pair <Nat : Type, x : Nat>
def h1 (x : Nat) : Σ a : Type, a := (f Type (fun α => α) Nat x)

#check f Type (fun α => α) Nat 1
#check g Type (fun Float => Float) String

#check @f
#check @g
#check @h1

#reduce h1 5
