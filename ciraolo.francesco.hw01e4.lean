import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

-- Ex 4.1

example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
  a = 2 * 3 + 5 := by rw[h1, h2]
  _ = 11 := by numbers

-- Ex 4.2

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
  x = 2 - 4 := by addarith[h1]
  _ = -2 := by numbers

-- Ex 4.3

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have h3 : b = 1 := by addarith[h2]
  calc
  a = 5 * b + 4 := by addarith[h1]
  _ = 5 * 1 + 4 := by rw[h3]
  _ = 9 := by numbers