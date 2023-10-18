import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
--   obtain hP | hQ := h1
--   · apply hP
--   · contradiction

-- example (P Q : Prop) : P → (P ∨ ¬ Q) := by
--   intro hP
--   left
--   apply hP

-- example (P : Prop) : (P ∨ P) ↔ P := by
--   constructor
--   · intro h
--     obtain h | h := h
--     · exact h
--     · exact h
--   · intro h
--     left
--     exact h
  
-- example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
--   constructor
--   · intros h
--     have ⟨ p, qr ⟩ := h
--     obtain q|r := qr
--     · left
--       exact { left := p, right := q }
--     · right
--       exact { left := p, right := r}
--   · intros h
--     obtain pq | pr := h
--     · have ⟨p,q⟩ := pq
--       exact { left := p, right := Or.inl q }
--     · have ⟨p,r⟩ := pr
--       exact { left := p, right := Or.inr r }

-- example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
--     ∀ x : α, P x ∧ Q x := by
--   intros x
--   constructor
--   · apply h1 x
--   apply h2 x

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  -- obtain ⟨k, hk⟩ := h
  · intros hx
    obtain ⟨x,hx⟩  := hx
    use x
    have h' := h x 
    obtain ⟨h',h''⟩  := h'
    apply h' hx
  · intros hx
    obtain ⟨x,hx⟩  := hx
    use x
    have h' := h x 
    obtain ⟨h',h''⟩  := h'
    apply h'' hx


example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intros h
    obtain ⟨x,y,h⟩ := h
    use y
    use x
    exact h
  · intros h
    obtain ⟨x,y,h⟩ := h
    use y
    use x
    exact h

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intros h y x
    apply  h x y
  intros h x y
  apply h y x

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intros h
    obtain ⟨x,q⟩ := h
    obtain ⟨x,px⟩ := x
    use x
    exact { left := px, right := q }
  · intros h
    obtain ⟨x,q⟩ := h
    obtain ⟨px,q⟩ := q
    constructor
    · use x
      exact px
    exact q

