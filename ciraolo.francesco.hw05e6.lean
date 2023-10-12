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

example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  · right
    -- have t := H m
    -- have t := (H m) hm_left
    -- have t'' := imp
    have t : ¬(m < p) := by
      intros t''
      exact H m hm_left t'' hmp
    -- have t : m ≥ p := Iff.mp Nat.not_lt t
    -- have t' := exists_eq_mul_left_of_dvd hmp
    -- obtain ⟨b, hb⟩ := t'
    have t'' : p ≥ m := Nat.le_of_dvd hp' hmp
    exact Nat.le_antisymm t'' (Iff.mp Nat.not_lt t)
  -- the case `1 < m`

  -- sorry


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y := by
      apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos



example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by

  obtain ha' | ha' := lt_or_ge 2 a
  · simp at ha'
    exact ha'

  obtain hb' | hb' := le_or_gt b 1
  · have t := calc
      c ^ 2 = a ^ 2 + b ^ 2 := by rw[h_pyth]
      _ ≤ 2 ^ 2 + 1 ^ 2 := by rel[hb', ha']
      _ <  3^2 := by numbers
    obtain ha'' | ha'' := le_or_gt a 1
    · have t' := calc
        a^2 + b^2 = 1^2 + 1^2 := by rw[(le_antisymm hb' hb), (le_antisymm ha'' ha)]
        _ = 2 := by numbers
      have h'' : c^2 = 2 := calc
        c^2 = a^2 + b^2 := by rw[h_pyth]
        _ = 2 := by rw[t']
      obtain hc' | hc' := le_or_gt c 1
      · have t'' := calc
          c^2 = 1^2 := by rw[le_antisymm hc' hc]
          _ = 1 := by numbers
        have tx : 1 ≠ 2 := Nat.ne_of_beq_eq_false rfl
        have t''' : c^2 ≠ 2 := ne_of_eq_of_ne t'' (tx)
        contradiction
      · have t'' := calc
          c^2 = 2^2 := by rw[le_antisymm (by exact hc') (Iff.mp Nat.lt_succ (lt_of_pow_lt_pow' 2 t))]
          _ = 4 := by numbers
        have tx : 4 ≠ 2 := Nat.ne_of_beq_eq_false rfl
        have t''' : c^2 ≠ 2 := ne_of_eq_of_ne t'' (tx)
        contradiction
    · have t' := calc
        a^2 + b^2 = 2^2 + 1^2 := by rw[(le_antisymm hb' hb), (Nat.le_antisymm ha' ha'')]
        _ = 5 := by numbers
      have h'' : c^2 = 5 := calc
        c^2 = a^2 + b^2 := by rw[h_pyth]
        _ = 5 := by rw[t']
      obtain hc' | hc' := le_or_gt c 1
      · have t'' := calc
          c^2 = 1^2 := by rw[le_antisymm hc' hc]
          _ = 1 := by numbers
        have tx : 1 ≠ 5 := Nat.ne_of_beq_eq_false rfl
        have t''' : c^2 ≠ 5 := ne_of_eq_of_ne t'' (tx)
        contradiction
      · have t'' := calc
          c^2 = 2^2 := by rw[le_antisymm (by exact hc') (Iff.mp Nat.lt_succ (lt_of_pow_lt_pow' 2 t))]
          _ = 4 := by numbers
        have tx : 4 ≠ 5 := Nat.ne_of_beq_eq_false rfl
        have t''' : c^2 ≠ 5 := ne_of_eq_of_ne t'' (tx)
        contradiction
        
  · have hb' : 2 ≤ b  := hb'
    have t := calc
      b^2 < a^2 + b^2 := by extra
      _ = c^2 := by rw[h_pyth]
    have t := lt_of_pow_lt_pow' 2 t
    have t' : b + 1 ≤ c := t
    have t'' := calc
      c^2 = a^2 + b^2 := by rw[h_pyth]
        _ ≤ 2^2 + b^2 := by rel[ha']
        _ = b^2 + 2 * 2 := by ring
        _ ≤ b^2 + 2 * b := by rel[hb']
        _ < b^2 + 2 * b + 1 := by extra
        _ = (b + 1)^2 := by linarith
        
    have t : c ≥ b + 1 := t
    have t'' : ¬(c ≥ b + 1) := Iff.mpr Nat.not_le (lt_of_pow_lt_pow' 2 t'')
    contradiction  

-- example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
--     (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
--   by_cases a ≤ 2
--   · have h' := h
--     by_cases b ≤ 1
--     · have t := calc
--         c ^ 2 = a ^ 2 + b ^ 2 := by rw[h_pyth]
--         _ ≤ 2 ^ 2 + 1 ^ 2 := by rel[h', h]
--         _ ≤  3^2 := by numbers
      
      
--       sorry
--     · simp at h
--       have h: 2 ≤ b := h
--       have t := calc
--         b ^ 2 < a^2 + b^2 := by extra
--         _ = c ^ 2 := by rw[h_pyth]

--       have ha' : 0 ≤ a := by exact Nat.zero_le a
--       have t'' := Iff.mp (sq_eq_sq (Nat.zero_le a) (Nat.zero_le b)) 
      

--       sorry
--   · simp at h
--     exact h

example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  exact le_of_pow_le_pow n hx hn h


-- example (p : ℕ) : 2 = 1 ∨ 2 = p → False ∨ 2 = p := by
--   intro h
--   obtain h | h := h
--   · have t'' : 2 = 1 ↔ False := by exact Iff.mp decide_eq_decide rfl
--     have h' : False := by apply Iff.mp t'' h
--     exact False.elim h'
--   · exact Iff.mpr (false_or_iff (2 = p)) h


example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain hp | hp : p = 2 ∨ p ≠ 2 := em (p = 2)
  · left
    exact hp
  · right
    -- exact (h.2 2) hp
    -- dsimp [Odd]
    -- have t := h.2
    dsimp [Prime] at h
    obtain ⟨h', h''⟩ := h

    -- have h' : 3 ≤ p := by
    --   obtain h' | h' := lt_or_eq_of_le h'
    --   · exact h'
    --   · exact False.elim (hp (id (Eq.symm h')))


    contrapose! hp
    have hp : Nat.Even p := Iff.mpr (Nat.even_iff_not_odd p) hp
    
    have h''' : 2 ∣ p := by
      have t'' : Nat.Even p ↔ 2 ∣ p := by simp [Nat.Even, Dvd.dvd, two_mul]
      apply Iff.mp t'' hp

    dsimp [Nat.Even] at hp

    have f' : 2 = 1 ∨ 2 = p → 2 = p ∨ False := by
      intro h
      obtain h | h := h
      · have t'' : 2 = 1 ↔ False := by exact Iff.mp decide_eq_decide rfl
        have h' : False := by apply Iff.mp t'' h
        exact False.elim h'
      · exact Iff.mpr (or_false_iff (2 = p)) h
    
    have t := f' (h'' 2 hp)
    simp at t
    exact id (Eq.symm t)
