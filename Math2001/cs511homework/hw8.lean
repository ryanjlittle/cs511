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
  · rel[h]
  · calc
      a ^ (k + 1) ≡ b ^ (k + 1) [ZMOD d] := by rel[h]

/- 3 points -/
theorem problem4b : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · calc
      2 ^(k+1) = 2*(2^k) := by ring
      _ ≥ 2*(k^2) := by rel[IH]
      _ = k^2 + k*k := by ring
      _ ≥ k^2 + 4*k := by rel[hk]
      _ = k^2 + 2*k + 2*k := by ring
      _ ≥ k^2 + 2*k + 2*4 := by rel[hk]
      _ = (k+1)^2 + 7 := by ring
      _ ≥ (k+1)^2 := by extra

/- 2 points -/
theorem problem4c {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · calc
      (1+a)^0 ≥ (1+(-1))^0 := by rel[ha]
      _ = 1 := by numbers
      _ = 1 + 0*a := by ring
  · have helper : 0 ≤ 1 + a := by addarith[ha]
    calc
      (1 + a) ^ (k + 1) = ((1+a)^k) * (1+a) := by ring
      _ ≥ (1+k*a) * (1+a) := by rel[IH]
      _ = 1 + k*a + a + k*a^2 := by ring
      _ ≥ 1 + k*a + a := by extra
      _ = 1 + (k+1)*a := by ring


/- 3 points -/
theorem problem4d : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers
  · calc
      (3:ℤ) ^ (k+1) = 3*3^(k) := by ring
      _ ≥ 3*(2^k + 100) := by rel[IH]
      _ = 3*2^k + 300 := by ring
      _ = 2^(k+1) + 100 + 200 + 2^k := by ring
      _ ≥ 2^(k+1) + 100 + 200 := by extra
      _ ≥ 2^(k+1) + 100 := by extra


/- 5 points -/
/-theorem problem5b : -/
/-complete the rest of the header on your own and provide the proof-/

def foo: ℕ → ℕ
  | 0 => 0
  | n + 1 => 2*n+1 + foo (n)

theorem problem5b {n : ℕ} : ∃ (k : ℕ), foo (n) = k ^ 2 := by
  use n
  simple_induction n with j IH
  dsimp [foo]
  · numbers
  · calc
      2*j + 1 + foo (j) = 2*j + 1 + j^2 := by rw[IH]
      _ = (j + 1) ^ 2 := by ring
