import Mathlib

namespace Lecture1

theorem add_mul_le_add_pow (n : ℕ) (c : ℤ) (hc : -1 ≤ c) (hn : 0 < n)
  : 1 + n * c ≤ (1 + c) ^ n := by
  --
  induction' hn with m _ hmm
  · -- base case
    simp

  · -- 1 + (↑k + 1) * c ≤ (1 + c) ^ (k + 1)
    calc 1 + (m + 1) * c
      _≤ 1 + (m + 1) * c + (m * c ^ 2) := by nlinarith
      _= 1 + m * c + c + m * c ^ 2 := by ring
      _= (1 + c) * (1 + m * c) := by ring
      _≤ (1 + c) * (1 + c) ^ m := by nlinarith
      _= (1 + c) ^ (m + 1) := by ring

end Lecture1
