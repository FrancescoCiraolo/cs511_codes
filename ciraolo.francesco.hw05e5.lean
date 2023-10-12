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


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers

example {n : ℕ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intros h
    constructor
    · refine Iff.mpr dvd_iff_exists_eq_mul_left ?mp.left.a
      use 63
      have h' := exists_eq_mul_right_of_dvd h
      obtain ⟨k, hk⟩ := h'

      obtain h'' | h'' := eq_or_ne k 7
      · rw[hk, h'']
      · simp at h''
        -- obtain t | t := ne_or_eq k 
        sorry
    · 
      sorry
  · intros h
    obtain ⟨h, h'⟩ := h
    simp at *
    sorry

example {n : ℕ} : 7 ∣ n ∧ 11 ∣ n → 77 ∣ n := by
  intros h
  sorry



example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor
  · intro y hy1 hy2
    have hy1' : y - 2 ≥ -1 := calc
      y - 2 ≥ 1 - 2 := by rel[hy1]
      _ = -1 := by numbers

    have hy2' : y - 2 ≤ 1 := calc
      y - 2 ≤ 3 - 2 := by rel[hy2]
      _ = 1 := by numbers

    calc
      (y - 2) ^ 2 ≤ 1 ^ 2 := sq_le_sq' hy1' hy2'
      _ = 1 := by numbers
  · intro y hy
    have t1 := hy 1
    have t := imp_eq_of_eq_true_left (1 ≥ 1) t1
    have t3 := hy 3
    sorry

example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  
  sorry


example : ∃! n : ℕ, ∀ a, n ≤ a := by
  sorry
