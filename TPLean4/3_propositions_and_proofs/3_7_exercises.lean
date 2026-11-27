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

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hl: (p ∨ q) ∨ r =>
      Or.elim hl
      (fun hll: p ∨ q =>
        Or.elim hll
          (fun hlll: p => Or.inl hlll)
          (fun hllr: q => Or.inr (Or.inl hllr)))
      (fun hlr: r => Or.inr (Or.inr hlr)))
    (fun hr: p ∨ (q ∨ r) =>
      Or.elim hr
      (fun hrl: p => Or.inl (Or.inl hrl))
      (fun hrr: q ∨ r =>
        Or.elim hrr
        (fun hrrl: q => Or.inl (Or.inr hrrl))
        (fun hrrr: r => Or.inr hrrr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun hl: p ∧ (q ∨ r) =>
      Or.elim hl.right
      (fun hll: q => Or.inl (And.intro hl.left hll))
      (fun hlr: r => Or.inr (And.intro hl.left hlr)))
    (fun hr: (p ∧ q) ∨ (p ∧ r) =>
      Or.elim hr
      (fun hrl: p ∧ q => And.intro hrl.left (Or.inl hrl.right))
      (fun hrr: p ∧ r => And.intro hrr.left (Or.inr hrr.right)))


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun hl: p ∨ (q ∧ r) =>
      Or.elim hl
      (fun hll: p => And.intro (Or.inl hll) (Or.inl hll))
      (fun hlr: q ∧ r => And.intro (Or.inr hlr.left) (Or.inr hlr.right)))
    (fun hr: (p ∨ q) ∧ (p ∨ r) =>
      Or.elim hr.left
      (fun hrll: p => Or.inl hrll)
      (fun hrlr: q =>
        Or.elim hr.right
        (fun hrlrl: p => Or.inl hrlrl)
        (fun hrlrr: r => Or.inr (And.intro hrlr hrlrr))
      )
    )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun hl: p → (q → r) => fun hpq: p ∧ q => hl hpq.left hpq.right)
    (fun hr: p ∧ q -> r => fun hp: p => fun hq: q => hr (⟨hp, hq⟩))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun hl: (p ∨ q) → r =>
      And.intro
        (fun hp: p => hl (Or.inl hp))
        (fun hq: q => hl (Or.inr hq)))
    (fun hr: (p → r) ∧ (q → r) => fun hpq: p ∨ q =>
      Or.elim hpq
      (fun hp: p => hr.left hp)
      (fun hq: q => hr.right hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun hl: ¬(p ∨ q) =>
      And.intro
        (fun hp: p => hl.elim (Or.inl hp))
        (fun hq: q => hl.elim (Or.inr hq)))
    (fun hr: ¬p ∧ ¬q => fun hpq: p ∨ q =>
      Or.elim hpq
      (fun hp: p => hr.left hp)
      (fun hq: q => hr.right hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun hnpq: ¬p ∨ ¬q =>
    Or.elim hnpq
      (fun hnp: ¬p => fun hpq: p ∧ q => hnp.elim hpq.left)
      (fun hnq: ¬q => fun hpq: p ∧ q => hnq.elim hpq.right)

example : ¬(p ∧ ¬p) :=
  fun hpnp: p ∧ ¬p => absurd hpnp.left hpnp.right

example : p ∧ ¬q → ¬(p → q) :=
  fun hpnq: p ∧ ¬q => fun hpq: p → q => hpnq.right (hpq hpnq.left)

example : ¬p → (p → q) :=
  fun hnp: ¬p => fun hp: p => absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
  fun hnpq: ¬p ∨ q =>
    Or.elim hnpq
    (fun hnp: ¬p => fun hp: p => absurd hp hnp)
    (fun hq: q => fun _: p => hq)

example : p ∨ False ↔ p :=
  Iff.intro
    (fun hpf: p ∨ False =>
      Or.elim hpf
      (fun hp: p => hp)
      (fun hf: False => False.elim hf))
    (fun hp: p => Or.inl hp)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun hpf: p ∧ False => hpf.right)
    (fun hf: False => False.elim hf)

example : (p → q) → (¬q → ¬p) :=
  fun hpq: p → q => fun hnq: ¬q => fun hp: p => absurd (hpq hp) hnq

-- proofs that require Classical reasoning
open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
