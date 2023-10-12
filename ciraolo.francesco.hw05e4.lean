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

-- Execises @ 4.2.10

-- Ex 1
example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    have h : 2 * x = 12 := by addarith[h]
    calc
      x = (2 * x) / 2 := by ring
      _ = 12 / 2 := by rw[h]
      _ = 6 := by numbers
  · intro h
    calc
      2 * x - 1 = 2 * 6 - 1 := by rw[h]
      _ = 11 := by numbers

-- Ex 2
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h
    refine Iff.mpr (and_iff_right ?mp.ha) ?mp.a
    · refine Iff.mpr dvd_iff_exists_eq_mul_left ?mp.ha.a
      -- use 9
      -- obtain ⟨b, hb⟩ := h

      have h' := exists_eq_mul_left_of_dvd h
      obtain ⟨b, hb⟩ := h'
      use 63
      
      -- have h'' : Exists.elim h'
      sorry
    · sorry
  · intro h
    obtain ⟨n7, n9⟩ := h

    sorry

example {k : ℕ} (h : k ^ 2 ≤ 6) : k ^ 2 < 6 ∨ k ^ 2 = 6 := by
  -- have h' := lt_or_eq_of_le h
  exact Nat.lt_or_eq_of_le h
  -- sorry

-- Ex 5
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    have h' := le_or_gt k 0 
    obtain h' | h' := h'
    · left
      simp at h'
      exact h'
    · right
      have h'' := le_or_gt k 1 
      obtain h'' | h'' := h''
      · left
        apply le_antisymm h'' (by addarith[h'])
      · right
        have h''' : ¬(k ≥ 3) := by
          intros t
          have t' : 3 * 2 ≥ 3 * k := calc
            3 * 2 = 6 := by ring 
            _ ≥ k ^ 2 := by rel[h] 
            _ = k * k := by ring 
            _ ≥ 3 * k := by rel [t] 
          cancel 3 at t'
          addarith[t, le_antisymm t' (by addarith[h''])]
        simp at h'''
        addarith[h'', h''']
  · intro h
    obtain h | h := h
    calc
      k ^ 2 = 0 ^ 2 := by rw[h]
      _ ≤ 6 := by numbers
    obtain h | h := h
    calc
      k ^ 2 = 1 ^ 2 := by rw[h]
      _ ≤ 6 := by numbers
    calc
      k ^ 2 = 2 ^ 2 := by rw[h]
      _ ≤ 6 := by numbers



