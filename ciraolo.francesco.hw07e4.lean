import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use


-- 4 (a)
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      2 ≤ n :=  hn
      _ < n + n := by extra
      _ = 2 * n := by ring
      _ ≤ n * n := by rel[hn]
      _ = n^2 := by ring

-- 4 (b)
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intros h'
    by_cases P ∧ ¬Q
    · apply h
    · apply False.elim
      apply h'
      intros p
      rw[not_and_or] at h
      obtain h | h := h
      · contradiction
      · rw [not_not] at h
        apply h
  · intros h' h''
    obtain ⟨p, nq⟩ := h'
    have h' :=  h'' p
    contradiction