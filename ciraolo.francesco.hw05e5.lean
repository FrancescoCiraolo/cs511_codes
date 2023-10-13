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




-- example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
--   use 2
--   dsimp
--   constructor
--   · intro y hy1 hy2
--     have hy1' : y - 2 ≥ -1 := calc
--       y - 2 ≥ 1 - 2 := by rel[hy1]
--       _ = -1 := by numbers

--     have hy2' : y - 2 ≤ 1 := calc
--       y - 2 ≤ 3 - 2 := by rel[hy2]
--       _ = 1 := by numbers

--     calc
--       (y - 2) ^ 2 ≤ 1 ^ 2 := sq_le_sq' hy1' hy2'
--       _ = 1 := by numbers
--   · intro y hy
--     have t1 := hy 1
--     have t := imp_eq_of_eq_true_left (1 ≥ 1) t1
--     have t3 := hy 3
--     sorry

example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  intro y hy
  calc 
    y = (4 * y - 3 + 3) / 4 := by ring
    _ = (9 + 3) / 4 := by rw[hy]
    _ = 3 := by numbers


example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · exact fun a ↦ Nat.zero_le a
  intros y hy
  exact Iff.mp Nat.le_zero (hy 0)
