import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


-- Ex 3.1

example {p q r : Prop} (h_pqr : p ∧ q → r) : p → (q → r) := by
  intros h_p h_q
  apply h_pqr
  exact ⟨h_p, h_q⟩

-- Ex 3.2
example {p q r : Prop} (h_pqr : p → (q → r)) : (p → q) → (p → r) := by
  intros h_pq h_p
  apply h_pqr
  exact h_p
  apply h_pq
  exact h_p

-- Ex 3.3
example {p q r : Prop} (h_pnqr : p ∧ ¬ q → r) (h_nr : ¬r) (h_p : p) : q := by
  by_cases h_q : q
  exact h_q
  have h_pnq : p ∧ ¬q := And.intro h_p h_q
  have h_r : r := by apply h_pnqr h_pnq
  contradiction
