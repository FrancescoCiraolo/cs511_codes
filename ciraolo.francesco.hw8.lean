import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

/- 2 points -/
theorem problem4a {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  ·
    -- dsimp [Int.ModEq] at *
    -- dsimp [.∣.] at *
    -- obtain ⟨x,hx⟩ := h
    use 0
    calc
      a ^ 0 - b ^ 0 = 1 - 1 := by ring
      _ = d * 0 := by ring
  ·
    dsimp [Int.ModEq] at *
    dsimp [.∣.] at *
    obtain ⟨x,hx⟩ := IH
    obtain ⟨y,hy⟩ := h
    use (a * x + b ^ k * y)
    calc
      a ^ (k + 1) - b ^ (k + 1) = a * (a^k - b ^ k) + b^k *(a - b) := by ring
      _ = a * (d * x) + b ^ k * (d * y) := by rw[hx, hy]
      _ = d * (a * x + b ^ k * y) := by ring

/- 3 points -/
theorem problem4b : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    -- have h' : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    -- have h'' : 2^(k + 1) = 2 * 2 ^ k := by ring
    -- rw[h']
    -- rw[h'']
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2*k^2 := by rel[IH]
      _ = k^2 + k * k := by ring
      _ ≥ k^2 + 4 * k := by rel[hk]
      _ = k^2 + 2*k + 2*k := by ring
      _ ≥ k^2 + 2*k + 2*4 := by rel[hk]
      _ = (k + 1)^2 + 7 := by ring
      _ ≥ (k + 1)^2 := by extra

/- 2 points -/
theorem problem4c {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · calc
      (1 + a) ^ 0 = 1 := by ring
      _ = 1 + 0 * a := by ring
    linarith
  ·

    have h : a * a ≥ 0 := calc
        a * a = a ^ 2 := by ring
        _≥ 0 := by apply sq_nonneg


    have pd : 0 ≤ 1 + a := calc
      0 = 1  +(- 1) := by ring
      _ ≤ 1  + a := by rel[ha]
    calc
      (1 + a) ^ (k + 1) = (1 + a) * (1 + a) ^ k := by ring
      _ ≥ (1 + a) * (1 + ↑k * a) := by rel[IH]
      _ = (1 + a) + (1 + a) * (↑k * a) := by ring
      _ = 1 + a + (↑k * a) + a * (↑k * a) := by ring
      _ = 1 + a + ↑k * a + a * ↑k * a := by ring
      _ = 1 + a + ↑k * a + a * a * ↑k:= by ring
      _ ≥ 1 + a + ↑k * a + 0 * ↑k:= by rel[h]
      _ = 1 + a + ↑k * a := by ring
      _ = 1 + (↑k + 1) * a := by ring

/- 3 points -/
theorem problem4d : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · have pd : 2 ^ k + 100 ≤ 3 ^ k := by linarith
    /-
    'calc' tactic failed, has type
      3 ^ (k + 1) ≥ 2 ^ (k + 1) + 100
    but it is expected to have type
      3 ^ (k + 1) ≥ 2 ^ (k + 1) + 100
    -/
    have pd' := calc
      3 ^ (k + 1) = 3 * 3 ^ k := by ring
      _ ≥ 3 * (2 ^ k + 100) := by rel[pd]
      _ = (2 ^ k + 100) + 2 * (2 ^ k + 100) := by ring
      _ = (2 ^ k + 100) + 2 * 2 ^ k + 100 + 100 := by ring
      _ = (2 ^ k + 100) + 2 ^ (k + 1) + 100 + 100 := by ring
      _ ≥ (2 ^ k + 100) + 2 ^ (k + 1) + 100 := by extra
      _ ≥ 2 ^ (k + 1) + 100 := by extra
    sorry

/- 5 points -/
def foo : ℕ → ℕ
  | 0     => 1
  | n + 1 => foo (n) + 2 * n + 3

theorem auxproblem5b {n : ℕ} : foo (n) = (n + 1) ^ 2 := by
  simple_induction n with k IH
  . dsimp [foo]
    numbers
  dsimp [foo]
  simp
  -- obtain ⟨j, h⟩ := IH
  rw[IH]
  calc
    (k + 1) ^ 2 + 2 * k + 3
      = k^2 + 2 * k + 1 + 2 * k + 3 := by ring
    _ = k^2 + 4 * k + 4 := by ring
    _ = (k + 2) ^ 2 := by ring

/- 5 points -/
theorem problem5b {n : ℕ} : ∃ (k : ℕ), foo (n) = k ^ 2 := by
  simple_induction n with k IH
  · dsimp [foo] at *
    use 1
    numbers
  · obtain ⟨j, hj⟩ := IH
    have t : foo k = (k + 1) ^ 2 := auxproblem5b
    use k + 2
    apply auxproblem5b
