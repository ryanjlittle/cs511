import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use


------------ PROBLEM 4 -----------

example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      2 < 2^2 := by numbers
      _ ≤ n^2 := by rel [hn] 

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro h
    constructor
    · by_cases hp : P
      · apply hp
      · have hcont : P → Q := by 
          intro hp'
          apply False.elim
          apply hp
          contradiction
        contradiction 
    · by_cases hq : Q
      · have hcont : P → Q := by 
          intro hp'
          apply hq
        contradiction 
      · apply hq
  · intro h
    obtain ⟨hp, hq⟩  := h
    intro hpq
    have hq : Q := by 
      apply hpq
      apply hp
    contradiction


-------------- PROBLEM 5 -------------------

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  intro h
  use k
  constructor
  · apply hk
  · constructor
    · apply hk1
    · apply hkp

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    have h := by apply prime_test hp2 H
    contradiction
  push_neg at H
  apply H