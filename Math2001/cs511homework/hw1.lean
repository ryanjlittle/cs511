import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

-- PROBLEM 3

-- PROBLEM 4
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by
  calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by numbers

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  calc 
    x = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by numbers

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  calc
    a = a - 5*b + 5*b := by ring
    _ = 4 + 5*b := by rw [h1]
    _ = 4 + 5*(b+2-2) := by ring
    _ = 4 + 5*(3-2) := by rw [h2]
    _ = 9 := by numbers