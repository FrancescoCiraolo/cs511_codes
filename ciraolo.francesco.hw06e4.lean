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



def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

theorem not_superpowered_zero : ¬ Superpowered 0 := by
  intro h
  have one_prime : Prime (0 ^ 0 ^ 0 + 1) := h 0
  conv at one_prime => numbers -- simplifies that statement to `Prime 1`
  have : ¬ Prime 1 := not_prime_one
  contradiction

theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring
  apply prime_two


theorem not_superpowered_three : ¬ Superpowered 3 := by
  intro h
  dsimp [Superpowered] at h
  have four_prime : Prime (3 ^ 3 ^ 0 + 1) := h 0
  conv at four_prime => numbers -- simplifies that statement to `Prime 4`
  have four_not_prime : ¬ Prime 4
  · apply not_prime 2 2
    · numbers -- show `2 ≠ 1`
    · numbers -- show `2 ≠ 4`
    · numbers -- show `4 = 2 * 2`
  contradiction



example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  by_cases h2 : Superpowered 2
  · use 2
    constructor
    · exact h2
    · apply not_superpowered_three
  · use 1
    constructor
    · apply superpowered_one
    · apply h2

-- Ex 5.2.7.1

def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

theorem tribalanced_zero : Tribalanced 0 := by
  dsimp [Tribalanced]
  intros n
  conv => ring
  numbers

theorem not_tribalanced_two : ¬ Tribalanced 2 := by
  -- dsimp [Tribalanced]
  intros h

  have wrong : (1 + 2 / 2) ^ 2 < 3 := h 2
  conv at wrong => numbers
  exact wrong

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h1 : Tribalanced 1
  · use 1
    constructor
    · exact h1
    · conv => numbers
      apply not_tribalanced_two
  · use 0
    constructor
    · apply tribalanced_zero
    · conv => numbers
      apply h1

-- Ex 5.2.7.3

theorem euler_discover_225 : ¬ Prime 4294967297 := by
  apply not_prime  641 6700417 (by numbers) (by numbers) (by numbers)

theorem not_superpowered_two : ¬ Superpowered 2 := by
  intro h
  dsimp [Superpowered] at h
  have n_euler_discover : Prime (2 ^ 2 ^ 5 + 1) := h 5
  conv at n_euler_discover => numbers
  contrapose! n_euler_discover
  apply euler_discover_225

example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  · exact superpowered_one
  apply not_superpowered_two