/-
One way in which Lean's dependent type theory extends simple type theory is that
types themselves, entities like Nat and Bool, are first-class citizens,
which is to say that they themselves are objects.
For that to be the case, each of them also has to have a type.
-/


-- each of these is an object of type "Type"
#check Nat
#check Bool
#check Float
#check Nat → Nat
#check Nat × Nat

-- declaring new constant for types
def α : Type := Nat
def β : Type := Nat → Nat
def γ : Type := Nat × Nat
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check β
#check γ
#check F α
#check G α Nat

-- the followings are the same type, lean just displays them differently
#check G α β
#check Prod α β
#check α × β

-- here are proofs that they are the same type
example : G α β = Prod α β := rfl
example : G α β = (α × β) := rfl
example : Prod α β = (α × β) := rfl

-- similarly the followings are the same
#check F α
#check List α

-- here is a proof that they are the same type
example : F α = List α := rfl

/-
Given that every type has a type, the question arises: what is the type of Type?
-/

#check Type

-- we have actually come up against one of the most subtle aspects of Lean's typing system.
-- Lean's underlying foundation has an infinite hierarchy of types:
#check Type
#check Type 1
#check Type 2
#check Type 3
#check Type 4
#check Type 5
#check Type 6
#check Type 7
#check Type 8
#check Type 9
#check Type 10
#check Type 11
#check Type 12
#check Type 13
#check Type 14
#check Type 15
#check Type 16
#check Type 17

-- Type is just an abbreviation for Type 0
#check Type
#check Type 0
example : Type = Type 0 := rfl

-- we can think of Type 0 as a universe of "small" or "ordinary" types.
-- Type 1 as a universe of "larger" types that include Type 0 as an element.
-- Type 2 as a universe of even "larger" types that include Type 1, and so on.
-- The list is infinite: there is a Type n for every natural number n.


/-
The following table may help concretize the relationships being discussed.
Movement along the x-axis represents a change in the universe,
while movement along the y-axis represents a change in what is sometimes referred to as "degree".

| sort | Prop (Sort 0) | Type (Sort 1) | Type 1 (Sort 2) | Type 2 (Sort 3)        | ... |
|------|---------------|---------------|-----------------|------------------------|-----|
| type | True          | Bool          | Nat -> Type     | Type -> Type 1         | ... |
| term | True.intro    | true          | fun n => Fin n  | fun (_ : Type) => Type | ... |
-/


/-
Some operations, however, need to be polymorphic over type universes.
For example, List α should make sense for any type α, no matter which type universe α lives in.
This explains the type signature of the function List:
-/

-- whenever α has type Type u, List α also has type Type u
#check List

-- for Prod α β, whenever α has type Type u and β has type Type v, Prod α β has type Type (max u v)
#check Prod


/-
To define polymorphic constants, Lean allows you to declare universe variables explicitly using the universe command:
-/

universe u

def f (α : Type u) : Type u := Prod α α
def f2.{w} (α : Type w) : Type w := List α -- the "{w}" is the universe variable declaration, it can be omitted

#check f
#check f2
