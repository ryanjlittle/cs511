import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

------ PROBLEM 4 -------------

example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  have hxt'' := 
    calc 
      0 < (-x) * t := by addarith [hxt] 
      _ = x * (-t) := by ring 
  cancel x at hxt'' 
  have ht : t < 0 := by addarith [hxt''] 
  apply ne_of_lt 
  apply ht 


example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1
  use a 
  calc 
    (a+1)^2 - a^2 = a^2 + 2*a + 1 - a^2 := by ring 
    _ = 2*a + 1 := by ring 


example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  have ppq2 := 
    calc
      p = (p+p) / 2 := by ring
      _ < (p+q) / 2 := by rel [h] 
  apply ppq2 
  have pq2q := 
    calc
      (p+q) / 2 < (q+q) / 2 := by rel [h]
      _ = q := by ring 
  apply pq2q 

