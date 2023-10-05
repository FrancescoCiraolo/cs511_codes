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

-- example : Odd (7:ℤ) := by
--   dsimp [Odd]
--   use 3
--   numbers

-- example : Odd (-3:ℤ) := by
--   dsimp [Odd]
--   use -2
--   numbers

-- example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
--   dsimp [Odd] at *
--   obtain ⟨k, hk⟩ := hn
--   use 3 * k  + 2
--   calc
--     3 * n + 2
--       = 3 * (2 * k + 1) + 2 := by rw [hk]
--     _ = 2 * (3 * k + 2) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4
      = 7 * (2 * k + 1) - 4 := by rw[hk]
    _ = 2 * (7 * k + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨kx, hkx⟩ := hx
  obtain ⟨ky, hky⟩ := hy
  use 2 * kx * ky + 3 * ky + kx + 1
  calc
    x * y + 2 * y
      = (2 * kx + 1) * y + 2 * y := by rw[hkx]
    _ = (2 * kx + 1) * (2 * ky + 1) + 2 * (2 * ky + 1) := by rw[hky]
    _ = 2 * (2 * kx * ky + 3 * ky + kx + 1) + 1 := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  calc
    n ^ 2 + 2 * n - 5
      = (k + k) ^ 2 + 2 * (k + k) - 5 := by rw[hk]
    _ = 2 * (2 * k ^ 2 + 2 * k - 3) + 1 := by ring

-- example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
--   have h1 :=
--     calc
--     (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
--     _ = 0 := by rw [hx]
--   have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1

--   sorry

-- le_antisymm


example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by

  by_cases hab : Even (a - b)
  left
  exact hab

  by_cases hac : Even (a + c)
  right
  left
  exact hac
  by_cases hbc : Even (b - c)
  right
  right
  exact hbc
  sorry

