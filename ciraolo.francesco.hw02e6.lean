import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

-- Ex 1 
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
    x = x + 3 - 3 := by ring
    _ ≥ 2 * y - 3 := by rel [h1]
    _ ≥ 2 * 1 - 3 := by rel [h2]
    _ = -1        := by numbers   

-- Ex 2
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = 
    sorry


-- Ex 3
example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x
      = x * x * x - 8 * x * x + 2 * x := by ring
    _ ≥ 9 * x * x - 8 * x * x + 2 * 9 := by rel [hx]
    _ = x * x + 2 * 9 := by ring
    _ ≥ 9 * 9 + 2 * 9 := by rel[hx]
    _ ≥ 3 := by numbers 