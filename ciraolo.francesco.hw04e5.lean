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

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

-- example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
--   calc
--     a ≤ 1 ^ 2 - 2 * 1 := by apply h
--     _ = -1 := by numbers

-- example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
--   have h1 : n ∣ 1 := by apply hn
--   have h2 : 0 < 1 := by numbers
--   apply le_antisymm
--   · apply Nat.le_of_dvd h2 h1
--   · apply Nat.pos_of_dvd_of_pos h1 h2

example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h': (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain hx | hy := h'
  · calc
    b = 2 * (( a + b ) / 2) - a := by ring
    _ ≥ 2 * a - a := by rel[hx]
    _ = a := by ring
  · calc
    a = 2 * (( a + b ) / 2) - b := by ring
    _ ≤ 2 * b - b := by rel[hy]
    _ = b := by ring



example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by extra
    _ = x ^ 2 - 2 * x := by ring

-- example {a b : ℝ} : (x + y)^2 ≤ (x + y)^2 + (x - y)^2 := by
--   sorry

example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intros x y h
  
  -- have h': (x + y)^2 < 3^2
  -- calc
  --   (x + y)^2 ≤ (x + y)^2 + (x - y)^2 := by apply?
  -- calc
  --   (x + y)^2 
  --       ≤ (x + y)^2 - (x - y)^2 := by linarith
  --     _ = 2 * (x + y)^2 := by linarith
  --     _ ≤ 2 * 4 := by rel[h]

  -- have h' := by apply abs_le_of_sq_le_sq' h
  sorry

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  
  sorry

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  apply?
  sorry