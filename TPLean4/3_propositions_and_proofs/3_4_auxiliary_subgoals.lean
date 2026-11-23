variable (p q : Prop)

-- have construct introduce an auxiliary subgoal in a proof

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

/-
have proves a small fact, names it, and lets the rest of the proof use it.

  have hp : p := h.left    -- prove p (from h.left) and name it hp
  have hq : q := h.right   -- prove q (from h.right) and name it hq
  And.intro hq hp          -- use hp and hq to prove q ∧ p

Each have adds a name to the context, which the infoview shows at the cursor:

  | Cursor position     | Context              | Goal      |
  |---------------------|----------------------|-----------|
  | Start of the proof  | h : p ∧ q            | ⊢ q ∧ p   |
  | After have hp       | h, hp : p            | ⊢ q ∧ p   |
  | After have hq       | h, hp, hq : q        | ⊢ q ∧ p   |
  | Inside h.left       | h : p ∧ q            | ⊢ p       |

Tip: put _ or sorry where a proof is missing to see the goal at that spot.

Internally, have is just fun + application:

  have hp : p := h.left; rest of the proof
  becomes
  (fun (hp : p) => rest of the proof) h.left

So the proof above is the same as:
-/
example (h : p ∧ q) : q ∧ p :=
  (fun (hp : p) =>
    (fun (hq : q) => show q ∧ p from And.intro hq hp) h.right) h.left


-- suffices introduces a new goal that is sufficient to prove the main goal.
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h

/-
suffices is have in the opposite order: use the fact first, prove it last.

  suffices hq : q from And.intro hq hp   -- "if I had hq : q, I could finish with And.intro hq hp"
  show q from And.right h                -- now prove q

Compare with have, same proof:

  have hq : q := And.right h             -- prove q first
  And.intro hq hp                        -- then use it

Internally, both become the same fun + application:

  (fun (hq : q) => And.intro hq hp) (And.right h)

So the proof above is the same as:
-/

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  (fun (hq : q) => show q ∧ p from And.intro hq hp) (show q from And.right h)
