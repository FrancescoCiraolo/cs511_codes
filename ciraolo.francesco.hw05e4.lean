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

-- Ex 2
example {n : ℕ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intros h
    constructor
    · have t : 7 ∣ 63 := by exact Iff.mpr (Nat.dvd_iff_div_mul_eq 63 7) rfl
      exact Nat.dvd_trans t h
    · have t : 9 ∣ 63 := by exact Iff.mpr (Nat.dvd_iff_div_mul_eq 63 9) rfl
      exact Nat.dvd_trans t h
  · intros h
    obtain ⟨h7, h9⟩ := h
    dsimp [(.∣.)] at *
    obtain ⟨a,ha⟩ := h7 
    obtain ⟨b,hb⟩ := h9
    use 4 * b - 3 * a
    -- have : n = n + n - n := by ring
    have t : 27 * n = 63 * (3 * a) := calc
      27 * n = 27 * (7 * a) := by rw[ha]
      _ = 63 * (3 * a) := by ring
    calc
      n = n + 27 * n - 27 * n := by exact Eq.symm (Nat.add_sub_cancel n (27 * n))
      _ = 28 * n - 27 * n := by ring
      _ = 28 * n - 63 * (3 * a) := by rw[t]
      _ = 28 * (9 * b) - 63 * (3 * a) := by rw[hb]
      _ = 63 * (4 * b) - 63 * (3 * a) := by ring
      _ = 63 * (4 * b - 3 * a) := by exact Eq.symm (Nat.mul_sub_left_distrib 63 (4 * b) (3 * a))


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



