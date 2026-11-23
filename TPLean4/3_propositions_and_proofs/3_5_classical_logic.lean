/-
Classical logic

So far, every proof has been something we BUILD (this is called "constructive"):

  | To prove | We build                               |
  |----------|----------------------------------------|
  | p → q    | a function: fun hp : p => (proof of q) |
  | p ∧ q    | a pair: ⟨hp, hq⟩                        |
  | p ∨ q    | Or.inl hp  or  Or.inr hq               |
  | ¬p       | a function: fun hp : p => (proof of False) |

Note the p ∨ q row: to prove an "or", we must pick a side AND give a proof of that side.

Law of the excluded middle: p ∨ ¬p
  "Every statement is either true or false."

With only the rules above, we can't prove this for an arbitrary p:
  - Or.inl needs a proof of p
  - Or.inr needs a proof of ¬p
  and for an unknown p we have neither.

Isn't p ∨ ¬p obviously true?
  In Lean, "true" means "has a proof we can build".
  A built proof of p ∨ ¬p would have to say WHICH side is true, for every p.
  For open problems (e.g. Goldbach's conjecture) nobody knows which side,
  so we can't build that proof.

  | Logic        | p ∨ ¬p means                          | Provable?          |
  |--------------|---------------------------------------|--------------------|
  | Classical    | every statement is true or false      | yes (accepted)     |
  | Constructive | I can show which one, with a proof    | not in general     |

Why use it? Not for its own sake, but to split a proof into two cases:
  "suppose p is true ..." and "suppose p is false ...",
  even when we don't know which case holds (see double negation below).

Classical logic accepts p ∨ ¬p as true for every p. In Lean it is called Classical.em.
(Lean proves it from an extra axiom called choice, covered in Chapter 12.)
`open Classical` lets us write `em` instead of `Classical.em`.
-/

open Classical

variable (p q : Prop)

#check em        -- Classical.em (p : Prop) : p ∨ ¬p

-- for any p, we get p ∨ ¬p without knowing which side is true
example : p ∨ ¬p := em p

/-
Double negation elimination: ¬¬p → p
  "If p is not false, then p is true."

What h can do:
  ¬¬p means ¬p → False, which is (p → False) → False.
  So h is a function with one use: give it a proof of ¬p, and it returns False.

Why we need em:
  - To prove p, we need something that produces a p.
  - h produces only False, and only when we give it a ¬p.
  - We have no ¬p to give it, and no other source of p.
  So there's no way to get from h to p with the constructive rules alone.

em p fills the gap by splitting into two cases:

  | Case        | We have    | How we get p                               |
  |-------------|------------|--------------------------------------------|
  | p is true   | hp : p     | just return hp                             |
  | p is false  | hnp : ¬p   | h hnp : False, and False proves anything   |
                                (absurd hnp h does this)

The other direction, p → ¬¬p, does NOT need em:
  fun hnp : ¬p => hnp hp
-/
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

-- by cases is a function that takes two functions as arguments and returns a proof of p
#check byCases

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

-- by contradiction is a function that takes a function from ¬p to False and returns a proof of p
#check byContradiction

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p => show False from h h1)

/-
De Morgan's law: ¬(p ∧ q) → ¬p ∨ ¬q
  "If p and q are not both true, then p is false or q is false."

To prove an "or" we must pick a side, but h only says "not both",
so it doesn't tell us which side. em p splits it into two cases:

  | Case        | Reasoning                                     | Proof          |
  |-------------|-----------------------------------------------|----------------|
  | p is true   | q must be false, else p ∧ q contradicts h     | Or.inr (¬q)    |
  | p is false  | we already have ¬p                            | Or.inl hp      |

How the ¬q proof works (case p is true, so hp : p):
  show ¬q from fun hq : q => h ⟨hp, hq⟩

  ¬q means q → False, so we need a function from a proof of q to False:
    hq          : q             suppose q is true
    ⟨hp, hq⟩    : p ∧ q         with hp, we get p ∧ q
    h ⟨hp, hq⟩  : False         but h says p ∧ q is false: contradiction
  So fun hq : q => h ⟨hp, hq⟩ has type q → False, which is ¬q.
-/
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from fun hq : q => h ⟨hp, hq⟩))
    (fun hp : ¬p => Or.inl hp)
