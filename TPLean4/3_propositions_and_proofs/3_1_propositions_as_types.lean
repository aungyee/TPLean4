/-
Lean uses the same language of dependent type theory for mathematical definitions, statements, and proofs.

we introduce a new type call Prop to represent Statements (propositions).
-/

-- proposition
#check Prop

-- propositions and Nat are both in Type 0
#check Prop
#check Nat

-- Prop is just an abbreviation for Sort 0
#check Sort 0
example : Prop = Sort 0 := rfl

-- Sort 1 is Type 0
#check Sort 1
#check Type
example : Type = Sort 1 := rfl

/-
Constructors are introduced to build new propositions from existing ones.
-/

-- And, Or, Not are already defined in the core library
#check And
#check Or
#check Not

-- Implication is defined as a function type
def Implies (p q : Prop) : Prop := p → q

#check Implies

-- compound statements
variable (p q r : Prop)

#check And p q
#check Or (And p q) r
#check Implies (And p q) (And q p)


/-
We could then introduce, for each element p : Prop, another type Proof p, for the type of proofs of p.
An “axiom” would be a constant of such a type.
-/

structure Proof (p : Prop) : Type where
  proof : p

#check Proof

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

#check and_commut p q

-- modus ponens (From a proof of Implies p q and a proof of p, we obtain a proof of q)
axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p → Proof q

-- direct proof
-- if assuming p we can prove q, then we can prove Implies p q
axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)


/-
This approach would provide us with a reasonable way of building assertions and proofs.
Determining that an expression t is a correct proof of assertion p would then simply be a matter of checking that t has type Proof p.
-/

/-
Some simplifications are possible, however.
To start with, we can avoid writing the term Proof repeatedly by conflating Proof p with p itself.
In other words, whenever we have p : Prop, we can interpret p as a type, namely, the type of its proofs.

We can then read t : p as the assertion that t is a proof of p.
-/

axiom and_commut' (p q : Prop) : Implies (And p q) (And q p)
axiom modus_ponens' (p q : Prop) : (Implies p q) → p → q
axiom implies_intro' (p q : Prop) : (p → q) → (Implies p q)

/-
Moreover, once we make this identification, the rules for implication show that
we can pass back and forth between Implies p q and p → q.
In other words, implication between propositions p and q corresponds to
having a function that takes any element of p to an element of q.

As a result, the introduction of the connective Implies is entirely redundant:
  we can use the usual function space constructor p → q from dependent type theory as our notion of implication.
-/

axiom and_commut'' (p q : Prop) : And p q → And q p
axiom modus_ponens'' (p q : Prop) : (p → q) → p → q
axiom implies_intro'' (p q : Prop) : (p → q) → (p → q)

-- two proofs of the same proposition are equal (proof irrelevance)
example (p : Prop) (h1 h2 : p) : h1 = h2 := rfl
