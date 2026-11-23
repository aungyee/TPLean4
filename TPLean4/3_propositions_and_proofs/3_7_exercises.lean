variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun hp : p ∧ q => ⟨hp.right, hp.left⟩)
    (fun hq : q ∧ p => ⟨And.right hq, And.left hq⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun hp: p ∨ q =>
      Or.elim hp
        (fun hpl: p => Or.intro_right q hpl)
        (fun hql: q => Or.intro_left p hql))
    (fun hq: q ∨ p =>
      Or.elim hq
        (fun hqr: q => Or.intro_right p hqr)
        (fun hpr: p => Or.intro_left q hpr))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun hl: (p ∧ q) ∧ r => ⟨hl.left.left, ⟨hl.left.right, hl.right⟩⟩)
    (fun hr: p ∧ (q ∧ r) => ⟨⟨hr.left, hr.right.left⟩, hr.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry


-- proofs that require Classical reasoning
open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
