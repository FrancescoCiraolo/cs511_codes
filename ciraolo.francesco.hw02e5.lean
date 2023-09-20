import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


-- Ex 5.3

example {p q : Prop} : ¬ p ∧ ¬ q  → ¬ (p ∨ q) := by
  intros h1 h2
  obtain ⟨np, nq⟩ := h1
  obtain p | q := h2
  contradiction
  contradiction

-- Ex 5.4

example {p q : Prop} : ¬ p ∨ ¬ q  → ¬ ( p ∧  q) := by
  intros h1
  obtain np | nq := h1
  · intro h2
    obtain ⟨np, nq⟩ := h2
    contradiction
  · intro h2
    obtain ⟨np, nq⟩ := h2
    contradiction