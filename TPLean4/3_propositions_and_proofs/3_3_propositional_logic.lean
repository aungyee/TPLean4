/-

Lean defines all the standard logical connectives and notation.
The propositional connectives come with the following notation:

| ASCII | Unicode | Editor shortcut | Definition |
|-------|---------|-----------------|------------|
| True  |         |                 | True       |
| False |         |                 | False      |
| Not   | ¬       | \not, \neg      | Not        |
| /\    | ∧       | \and            | And        |
| \/    | ∨       | \or             | Or         |
| ->    | →       | \to, \r, \imp   |            |
| <->   | ↔       | \iff, \lr       | Iff        |

-/

variable (p q r : Prop)

-- examples
#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p


/-
Order of operations (1 = binds most strongly):

| Order | Symbol | Meaning     | Groups       |
|-------|--------|-------------|--------------|
| 1     | ¬      | not         | (one input)  |
| 2     | ∧      | and         | to the right |
| 3     | ∨      | or          | to the right |
| 4     | →      | implies     | to the right |
| 5     | ↔      | iff         | needs brackets to chain |

Example:
  a ∧ b → c ∨ d ∧ e   means   (a ∧ b) → (c ∨ (d ∧ e))

"Groups to the right" means:
  p → q → r   means   p → (q → r)   "if p, then if q, then r"
This is the curried form of p ∧ q → r.
-/

example (a b c d e : Prop) : (a ∧ b → c ∨ d ∧ e) = ((a ∧ b) → (c ∨ (d ∧ e))) := rfl


/-
Conjunctions
-/

-- And.intro builds a proof of p ∧ q from proofs of p and q (and-introduction rule)
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

-- And.left h creates a proof of p from a proof of p ∧ q (left and-elimination rule)
example (h : p ∧ q) : p := And.left h

-- And.right h creates a proof of q from a proof of p ∧ q (right and-elimination rule)
example (h : p ∧ q) : q := And.right h

-- We can now prove p ∧ q → q ∧ p with the following proof term
example (h : p ∧ q) : q ∧ p := And.intro (And.right h) (And.left h)


-- ⟨hp, hq⟩ is a convenient notation for And.intro hp hq
-- ⟨...⟩ is called anonymous constructor notation and works for any type that has exactly one constructor
variable (hp : p) (hq : q)
#check (⟨hp, hq⟩ : p ∧ q)

-- given an expression e of an inductive type Foo, e.field is notation for Foo.field e
variable (xs : List Nat)
#check List.length xs
#check xs.length

-- As a result, given h : p ∧ q, we can write h.left for And.left h and h.right for And.right h.
-- We can therefore rewrite the sample proof above conveniently as follows:
example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

-- right associativity of conjunction
example (h : p ∧ q) : q ∧ p ∧ q := ⟨h.right, ⟨h.left, h.right⟩⟩
example (h : p ∧ q) : q ∧ p ∧ q := ⟨h.right, h.left, h.right⟩

/-
Disjunctions
-/

-- Or.intro_left q hp builds a proof of p ∨ q from a proof of p (left or-introduction rule)
example (hp : p) : p ∨ q := Or.intro_left q hp

-- Or.intro_right p hq builds a proof of p ∨ q from a proof of q (right or-introduction rule)
example (hq : q) : p ∨ q := Or.intro_right p hq

-- The or-elimination rule is slightly more complicated.
-- we can prove p ∨ q → r, by showing that r follows from p and that r follows from q.
-- In other words, it is a proof by cases.
-- Or.elim takes three arguments -
--    h : p ∨ q
--    hpr : p → r
--    hqr : q → r
-- and produces a proof of r.
example (h : p ∨ q) : q ∨ p :=
  Or.elim
    h
    (fun hp : p => show q ∨ p from Or.intro_right q hp)
    (fun hq : q => show q ∨ p from Or.intro_left p hq)

-- the definition of Or.elim
#print Or.elim


-- Or.intro_left and Or.intro_right are also written as Or.inl and Or.inr
-- notice that lean infer the type of the arguments from the type of the constructor
example (h : p ∨ q) : q ∨ p := Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

-- h.elim is a convenient notation for Or.elim h
example (h : p ∨ q) : q ∨ p := h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

/-
Negations and Falsity
-/

-- ¬p is defined as a function type p → False
-- so a proof of ¬p is obtained by deriving a contradiction from p (negation introduction rule)
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

-- hnp hp : False, since ¬p means p → False (negation elimination rule)
-- False.elim turns a proof of False into a proof of any proposition q (false elimination rule)
-- becasue False → q is true for any q, by the truth table for implication
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

-- a convenient notation for False.elim (hnp hp) is absurd hp hnp
example (hp : p) (hnp : ¬p) : q := absurd hp hnp


-- proof for ¬p → q → (q → p) → r
example (hnp : ¬p) (hq : q) (hqp : q → p) : r := absurd (hqp hq) hnp

-- False has only an elimination rule
-- True has only an introduction rule

/-
Logical Equivalence
-/

-- Iff.intro builds a proof of p ↔ q from proofs of p → q and q → p (iff-introduction rule)
theorem and_commut : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_commut p q

-- Iff.mp applies a proof of p ↔ q to a proof of p to yield a proof of q (iff-elimination rule)
variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_commut p q) h

-- Iff.mpr applies a proof of p ↔ q to a proof of q to yield a proof of p (iff-elimination rule)
variable (h : q ∧ p)
example : p ∧ q := Iff.mpr (and_commut p q) h

-- ⟨...⟩ is also used to build proofs of p ↔ q as Iff only has one constructor
theorem and_commut' : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

-- h.mp and h.mpr are convenient notations for Iff.mp h and Iff.mpr h
example (h : p ∧ q) : q ∧ p := (and_commut' p q).mp h

/-

Summary: introduction (build a proof) and elimination (use a proof) rules

| Connective | Rule  | Lean                                    | Short form    |
|------------|-------|-----------------------------------------|---------------|
| p → q      | intro | fun hp : p => (proof of q)              |               |
|            | elim  | h hp : q                                |               |
| p ∧ q      | intro | And.intro hp hq                         | ⟨hp, hq⟩      |
|            | elim  | And.left h : p                          | h.left, h.1   |
|            | elim  | And.right h : q                         | h.right, h.2  |
| p ∨ q      | intro | Or.intro_left q hp                      | Or.inl hp     |
|            | intro | Or.intro_right p hq                     | Or.inr hq     |
|            | elim  | Or.elim h (fun hp => ..) (fun hq => ..) | h.elim        |
| ¬p         | intro | fun hp : p => (proof of False)          |               |
|            | elim  | hnp hp : False                          |               |
| False      | elim  | False.elim hf : q                       | absurd hp hnp |
| True       | intro | True.intro                              | trivial       |
| p ↔ q      | intro | Iff.intro hpq hqp                       | ⟨hpq, hqp⟩    |
|            | elim  | Iff.mp h : p → q                        | h.mp          |
|            | elim  | Iff.mpr h : q → p                       | h.mpr         |

False has no intro rule, True has no elim rule.

-/
