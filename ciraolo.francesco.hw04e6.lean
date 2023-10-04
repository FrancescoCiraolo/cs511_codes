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


example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have h : (x + 3) * (x - 2) = 0 := calc
      (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
      _ = 0 := h
    have h := eq_zero_or_eq_zero_of_mul_eq_zero h
    obtain h0 | h1 := h
    · left 
      linarith[h0]
    · right
      linarith[h1]
  · intro h
    have h' : x ^ 2 + x - 6 = (x + 3) * (x - 2) := by ring
    obtain h0 | h1 := h
    · 
      calc
        x ^ 2 + x - 6 = (x + 3) * (x - 2) := h'
        _ = (-3 + 3) * (x - 2) := by rw[h0]
        _ = 0 := by ring
    · calc
        x ^ 2 + x - 6 = (x + 3) * (x - 2) := h'
        _ = (x + 3) * (2 - 2) := by rw[h1]
        _ = 0 := by ring



example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    have h' : (2 * a - 5) ^ 2 ≤ 1^2 := calc
      (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤  4 * -1 + 5 := by rel[h]
      _ = 1^2 := by ring
    have h''' : (0:ℤ)  ≤ (1:ℤ)  := by numbers
    obtain ⟨hl, hh⟩ := abs_le_of_sq_le_sq' h' h'''
    have hl: 2 ≤ a := by linarith [hl]
    have hh: a ≤ 3 := by linarith [hh]
    have hx:= And.intro hl hh
    
    sorry
  · intro h
    obtain h0 | h1 := h

    · calc
      a ^ 2 - 5 * a + 5 = 2 ^ 2 - 5 * 2 + 5 := by rw[h0]
      _ ≤ -1 := by ring

    · calc
      a ^ 2 - 5 * a + 5 = 3 ^ 2 - 5 * 3 + 5 := by rw[h1]
      _ ≤ -1 := by ring