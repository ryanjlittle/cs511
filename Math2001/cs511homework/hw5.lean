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

-- Problem 4

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    constructor
    · use 9 * k
      calc
        n = 63 * k := by rw[hk]
        _ = 7 * (9 * k) := by ring
    · use 7 * k
      calc
        n = 63 * k := by rw[hk]
        _ = 9 * (7 * k) := by ring
  · intro h 
    obtain ⟨h7, h9⟩ := h 
    obtain ⟨k, hk7⟩ := h7 
    obtain ⟨l, hk9⟩ := h9
    use 4*l - 3*k
    calc
      n = 28*n - 27*n := by ring
      _ = 4*7*n - 3*9*n := by ring
      _ = 4*7*(9*l) - 3*9*n := by rw[hk9]
      _ = 4*7*(9*l) - 3*9*(7*k) := by rw[hk7]
      _ = 63*(4*l - 3*k) := by ring

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    obtain hkle2 | hkge3  := le_or_succ_le k 2
    · interval_cases k
      · left
        numbers
      · right
        left
        numbers 
      · right
        right
        numbers
    · have hcont := calc
        6 ≥ k^2 := by rel[h]
        _ ≥ 3^2 := by rel[hkge3]
        _ = 9 := by numbers
      contradiction 
  · intro h
    obtain h0 | h1 | h2 := h
    calc
      k^2 = 0^2 := by rw[h0]
      _ ≤ 6 := by addarith
    calc
      k^2 = 1^2 := by rw[h1]
      _ ≤ 6 := by addarith
    calc
      k^2 = 2^2 := by rw[h2]
      _ ≤ 6 := by addarith

-- Problem 5