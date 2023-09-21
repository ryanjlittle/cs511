import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

----------- PROBLEM 5 -----------------

lemma Problem5c {p q: Prop} : (¬ p ∧ ¬ q) → ¬(p ∨ q) := by 
  intros h1 h2
  obtain ⟨h_np, h_nq⟩ := h1 
  cases h2 with 
    | inr h_np => contradiction 
    | inl h_nq => contradiction 

lemma Problem5d {p q: Prop} : (¬ p ∨ ¬ q) → ¬(p ∧ q ) := by 
  intros h1 h2 
  obtain ⟨hp, hq⟩ := h2 
  cases h1 with 
    | inr hp => contradiction 
    | inl hq => contradiction 

----------- PROBLEM 6 -----------------

example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := by
  calc
    x = x + 3 - 3 := by ring
    _ ≥ 2 * y - 3 := by rel[h1]
    _ ≥ 2 * 1 - 3 := by rel[h2]
    _ = -1 := by numbers  

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := by
  calc
    a + b = 2*(a + b) / 2 := by ring
    _ = (a + b + a + b)/2 := by ring
    _ = (a + 2*b + a)/2 := by ring
    _ ≥ (4 + a)/2 := by rel[h2]
    _ ≥ (4+3)/2 := by rel[h1]
    _ ≥ 3 := by numbers    

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  calc 
    x^3 - 8*x^2 + 2*x = x*(x^2) - 8*x^2 + 2*x := by ring
    _ ≥ 9*x^2 - 8*x^2 + 2*x := by rel[hx]
    _ = x^2 + 2*x := by ring 
    _ ≥ 2*x := by extra
    _ ≥ 2*9 := by rel[hx] 
    _ ≥ 3 := by numbers 
