import Mathlib

import Pb100.Lecture5Util

namespace Lecture5

open Set Functor


namespace thm_2



-- · 0 ≤ x < y,
-- · x < 0 < y, and
-- · x < y ≤ 0.


theorem density_of_rationals (x y : ℝ) (hx : x < y) : ∃ r : ℚ, x < ↑r ∧ ↑r < y := by
  let m := (x + y) / 2
  obtain h | h | h := lt_trichotomy m 0
  · done
  · done
  · done

end thm_2




namespace thm_3

def S : Set ℝ := {1 - 1 / n | n > 0 }

lemma step2 (x : ℝ) (hx : x < 1) : ∃ m, 0 < (m:ℕ) ∧ x < 1 - 1 / m := by
  have ha := Real.instArchimedean
  rw [archimedean_iff_nat_lt] at ha

  have hx₁ : 0 < (1 - x) := by linarith
  have ha₁ := ha (1 / (1-x))
  have ⟨p, hp⟩ := ha₁

  use p

  have h₂ : 1 < p * (1 - x) := by exact (mul_inv_lt_iff₀ hx₁).mp hp
  have pos₁ : 0 < 1 - x := by nlinarith
  have pos₂ : (0:ℝ) < 1 := by norm_num
  have pos₃ : (0:ℝ) < p := by
    have := pos_of_lt_mul pos₂ pos₁ h₂
    aesop

  have h₃ : 1 / p < 1 - x := by rwa [bs_cancel_mul 1 p (1-x) pos₃]

  constructor
  · have pos₄ : (0:ℕ) < p := by aesop
    nlinarith
  · linarith

lemma step1 (x : ℝ) (h: x < 1) : x ∉ upperBounds S := by
  simp [S, upperBounds]
  have ⟨m, h₁, h₂⟩ := step2 x h
  use m
  constructor
  · simpa
  · simp at h₂; linarith


theorem theorem_3 : IsLUB S 1 := by
  constructor
  · -- 1 ∈ upperBounds S
    simp [upperBounds, S]
    intro a ha
    linarith

  · -- 1 ∈ lowerBounds (upperBounds S)
    intro x hx
    by_contra hc
    push_neg at hc
    have := step1 x hc
    contradiction

end thm_3


end Lecture5
