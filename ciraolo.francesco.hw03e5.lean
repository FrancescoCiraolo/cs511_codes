import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

example (x : ℝ) (hx : x > 0) : x^2 > x :=
  have hx_squared_pos : x^2 > 0 := pow_pos hx 2
  apply lt_trans hx hx_squared_pos

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have H := le_or_gt x 0
  obtain hx | hx := H
  · use 1
    linarith
  · use (x + 1)
    simp
    have px: 0 ≤ x := by exact LT.lt.le hx
    have sqx := calc
        x = x^1 := by simp
        _ < x^2 := pow_lt_pow_of_lt_left (lt_add_one x) px,
    have hx' := sq_pos_of_pos hx 
    have x' := sq_nonneg x
    have x'' := le_of_eq (sq_nonneg x)
    have hx'' := lt_of_le_of_lt (le_of_eq (sq_nonneg x)) (sq_pos_of_pos hx)
    sorry
    -- apply sq_pos_of_pos
    -- exact lt_of_le_of_lt (le_of_eq (sq_nonneg x)) (sq_pos_of_pos hx)
    

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt (x * t) (x + t)
  obtain hx | hx := H
  · 
    sorry
  · 
    sorry

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x, hxt⟩ := h
  
  have H := lt_or_ge (x) (3)
  obtain hx | hx := H
  · have hx'' := calc
      x < 3 := hx
      _ = 2 + 1 := by ring 

    have hx' := Iff.mp Int.lt_add_one_iff hx''
    apply ne_of_lt
    calc
        m = (2:Int) * x := by rel[hxt]
        _ ≤ (2:Int) * (2:Int) := by rel[hx']
        _ = (4:Int) := by ring
        _ < (5:Int) := by numbers
        
  · apply ne_of_gt
    calc
      (5:Int) < (6:Int) := by numbers
      _ = (2:Int) * (3:Int)  := by ring
      _ ≤ (2:Int) * x := by rel[hx]
      _ = m := by rel[hxt]