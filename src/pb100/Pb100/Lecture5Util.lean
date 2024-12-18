import Mathlib

namespace Lecture5

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by exact div_pos ha hb
example (z : ℝ) (ha : z ≠ 0) : (z⁻¹) * z = 1 := by exact inv_mul_cancel₀ ha


lemma bs_cancel_mul (a b c : ℝ) (h : 0 < b) : a / b < c ↔ a < b * c := by
  apply div_lt_iff₀' h

-- By the Archimedean property, there exists an n ∈ ℕ
-- such that 1 < n * (1 − x),
-- Therefore, ∃ m ∈ N such that x < 1 − 1 / m.

lemma pos_of_lt_mul {a b c : ℝ} (ha: 0 < a) (hc: 0 < c) : a < b * c → 0 < b := by
  intro h
  nlinarith


example (x y : ℝ) (h : 0 < x) : ∃ n : ℕ, y ≤ n * x := by
  obtain ⟨n, hn⟩ := Archimedean.arch y h
  use n
  have h₁ := nsmul_eq_mul n x
  -- inspect h₁ in the tactic state
  rwa [←h₁]


example (x y : ℝ) (h : 0 < x) : ∃ n : ℕ, y ≤ n * x := by
  obtain ⟨n, hn⟩ := Archimedean.arch y h
  use n
  rwa [← nsmul_eq_mul n x]

def real_rat (r : ℝ) := ∃ q : ℚ , r = q
def real_nat (r : ℝ) := ∃ n : ℕ , r = n
def real_int (r : ℝ) := ∃ z : ℤ , r = z

example : real_rat (1/2 : ℝ) := by
  unfold real_rat
  use 1 / 2
  ring

example : real_nat (1 : ℝ) := by
  unfold real_nat
  use 1
  ring


end Lecture5
