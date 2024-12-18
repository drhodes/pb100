import Mathlib

import Pb100.Lecture5Util

namespace Lecture5

open Set Functor

section thm_3

-- Proof :
-- step1) If n ∈ ℕ and 0 < n, then: 1 - 1/n < 1 → 1 ∈ upperBounds S.
-- Suppose that x is an upper bound for S.
-- We now prove that x ≥ 1.
-- For the sake of contradiction, assume that x < 1.
-- By the Archimedean property, there exists an n ∈ ℕ
-- such that 1 < n * (1 − x).

-- Therefore, ∃n ∈ N such that x < 1 − 1/n.
-- Hence, x is not an upper bound for the set S if x < 1.
-- Thus, if x is an upper bound, x ≥ 1.
-- Therefore: sup S = 1


noncomputable
def f (n : ℕ) : ℝ := 1 - 1 / n

def S := map f {n | n > 0 }

lemma step3 (x : ℝ) (hx : x < 1) : ∃ m, 0 < (m:ℕ) ∧ x < 1 - 1 / m := by
  have ha := Real.instArchimedean
  rw [archimedean_iff_nat_lt] at ha

  have hx₁ : 0 < (1 - x) := by linarith
  have ha₁ := ha (1 / (1-x))
  have ⟨p, hp⟩ := ha₁

  use p

  have h₂ : 1 < p * (1 - x) := by exact (mul_inv_lt_iff₀ hx₁).mp hp
  have pos₁ : 0 < 1 - x := by nlinarith
  have pos₂ : 0 < (1:ℝ) := by norm_num
  have pos₃ : (0:ℝ) < p := by
    have := pos_of_lt_mul pos₂ pos₁ h₂
    aesop

  have h₃ : 1 / p < 1 - x := by rwa [bs_cancel_mul 1 p (1-x) pos₃]

  constructor
  · have pos₄ : (0:ℕ) < p := by aesop
    nlinarith
  · linarith


lemma step2 (x : ℝ) : x < 1 → x ∉ upperBounds S := by
  intro hx₁
  simp [S, f, upperBounds]
  have ⟨m, h₁, h₂⟩ := step3 x hx₁
  use m
  constructor
  · exact h₁
  · --
    simp at h₂
    linarith

lemma step1 : 1 ∈ upperBounds S := by
  dsimp [upperBounds, S]
  simp [f]

theorem theorem_3 : IsLUB S 1 := by
  constructor
  · -- 1 ∈ upperBounds S
    exact step1
  · -- 1 ∈ lowerBounds (upperBounds S)
    intro x hx
    by_contra hc
    push_neg at hc
    have := step2 x hc
    contradiction









-- lemma xub : x ∈ upperBounds S := by
--   by_contra hc
--   dsimp [upperBounds] at hc
--   push_neg at hc
--   obtain ⟨r, ⟨hr₁, hr₂⟩⟩ := hc

--   simp [S, f] at hr₁
--   have ⟨q, hq⟩ := hr₁
--   have h01 : 1 ≤ q := by sorry
--   have h02 : 0 < x := by sorry
--   have hasdf := Archimedean.arch (1 - x) h02




-- theorem thm_3 : IsLUB S (1 : ℝ) := by
--   constructor
--   · --
--     intro a ⟨n, ⟨ha₁, ha₂⟩⟩
--     simp [f] at ha₂
--     rw [←ha₂]
--     norm_num
--   · --
--     dsimp [lowerBounds, upperBounds, S]
--     intro x hx
--     by_contra hc
--     push_neg at hc
--     have : 0 < ↑1 - x := by nlinarith
--     have ⟨m, hm⟩ := Archimedean.arch 1 this
--     rw [nsmul_eq_mul m (1 - x)] at hm
--     have hm₆ : 0 < 1 / (1 - x) := by
--       apply div_pos
--       linarith
--       linarith

--     have hm₀ : 1 / (1 - x) ≤ ↑m := by
--       rw [div_le_iff₀]
--       exact hm
--       exact this

--     have hm₈ :=
--       calc 0
--         _< 1 / (1 - x) := hm₆
--         _≤ ↑m := hm₀

--     let k : ℝ := (↑m)⁻¹

--     have h1 : 0 < (1:ℝ) := by norm_num
--     have : (0:ℝ) < 1 / (↑m) := by apply div_pos h1 hm₈
--     have : 0 < k := by aesop
--     have hm₉ : ↑m ≠ (0:ℝ) := by sorry
--     have hk₉ : k ≠ 0 := by aesop

--     have : k * 1 ≤ k * (↑m * (1 - x)) := by nlinarith
--     --have : 0 < x := by sorry
--     have :=
--       calc k
--         _≤ k * ↑m * (1 - x) := by nlinarith
--         _= (k * ↑m) * (1 - x) := by ring
--         _= ((↑m)⁻¹ * (↑m)) * (1 - x) := by dsimp [k]
--         _= (     ↑1      ) * (1 - x) := by rw [inv_mul_cancel₀ hm₉]
--         _= (1 - x) := by ring
--     have rawr : k - 1 + 2*x ≤ - x + 2*x := by nlinarith
--     have rawr₁ : k - 1 + 2*x ≤ x := by nlinarith

























end thm_3



--theorem thm_3 :

end Lecture5
