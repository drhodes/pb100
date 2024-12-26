import Mathlib

import Pb100.Lecture5Util

namespace Lecture5

open Set

namespace thm_2

lemma density1 (x y : ℝ) (h : 0 ≤ x ∧ x < y) : ∃ r : ℚ, x < r ∧ r < y :=  by
  have ha := Real.instArchimedean
  rw [archimedean_iff_nat_lt] at ha
  obtain ⟨n, hn⟩ := ha $ 1 / (y - x)
  obtain ⟨j, hj⟩ := ha $ 1 / n

  let S : Set ℕ := {k : ℕ | n * x < k}

  have hs : S.Nonempty := by aesop
  have ⟨hs₁, hs₂⟩ := isLeast_csInf hs
  let m := sInf S
  have : 0 < 1 / (y - x) := by aesop
  have hposn :=
    calc 0
      _< 1 / (y - x) := by aesop
      _< n := hn
  have : n * x < m := by aesop
  have hm₁ : m ≠ 0 := by aesop -- important!
  have hm : 0 ≤ m := by aesop
  have hm₂ : 0 < m := by exact Nat.zero_lt_of_ne_zero hm₁

  have : x < m / n := by exact (lt_div_iff₀' hposn).mpr hs₁

  -- since m is the least element, m - 1 is not in S.
  have : m < m + 1 := by linarith
  have : ↑m - (1:ℤ) < ↑m := by linarith

  have : m - 1 ∉ S := by
    dsimp [lowerBounds] at hs₂
    intro h
    have hs₃ := hs₂ h
    dsimp [m] at hs₃
    dsimp [m] at this

    suffices hs₅ : ¬ (sInf S ≤ sInf S - 1)
    contradiction
    --
    push_neg
    aesop

  let q : ℚ := m / n
  use q

  have hd₁ : x < ↑q := by
    dsimp [q]
    qify
    aesop

  have hd₂ : ↑q < y := by
    -- m - 1 ≤ n * x → m ≤ n * x + 1
    have : m - 1 ≤ n * x := by aesop
    dsimp [q]
    qify
    have : 1 < ↑n * (y - x) := by
      have : 0 < y - x := by aesop
      rw [bs_cancel_mul 1 (y - x) n this] at hn
      linarith
    have : m < n * y := by linarith
    have : m / n < y := by exact (bs_cancel_mul (↑m) (↑n) y hposn).mpr this
    exact this

  refine ⟨hd₁, hd₂⟩


lemma density2 (x y : ℝ) (h : x < y ∧ y ≤ 0) : ∃ r : ℚ, x < r ∧ r < y := by
  have hn : 0 ≤ -y ∧ -y < -x := by aesop
  obtain ⟨r, hy, hx⟩ := density1 (-y) (-x) hn
  use -r
  rify;
  refine ⟨by linarith, by linarith⟩


theorem density_of_rationals (x y : ℝ) (hx : x < y) : ∃ r : ℚ, x < ↑r ∧ ↑r < y := by
  obtain h | h | h := le_quintchotomy x y 0 hx
  · -- 0 ≤ x ∧ x < y
    exact density1 x y h
  · -- x < 0 ∧ 0 < y
    use 0;
    norm_cast
  · -- x < y ∧ y ≤ 0
    exact density2 x y h

end thm_2


namespace thm_3

noncomputable
def f (n : ℕ) : ℝ := 1 - 1 / n

def S := { f n | n > 0 }

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

end thm_3


namespace abs_koan

#check abs

variable (x y : ℝ)

-- Memorize these lemmas

example {x : ℝ} (h : 0 ≤ x) : |x| = x := abs_of_nonneg h
example {x : ℝ} (h : x ≤ 0) : |x| = -x := abs_of_nonpos h
example {x : ℝ} (h : 0 < x) : |x| = x := abs_of_pos h
example {x : ℝ} (h : x < 0) : |x| = -x := abs_of_neg h
example {x : ℝ} : |x| = 0 ↔ x = 0 := abs_eq_zero
example : |(0:ℝ)| = 0 := by exact abs_zero


theorem t1 : 0 ≤ |x| ∧ |x| = 0 ↔ x = 0 := by
  constructor
  · intro ⟨h₁, h₂⟩
    rwa [abs_eq_zero] at h₂
  · intro h
    constructor
    · rw [h, abs_zero]
    · rw [h, abs_zero]

theorem t2 : |-x| = |x| := by
  obtain h | h := le_or_lt x 0
  · rw [abs_of_nonpos h]
    have hx : 0 ≤ -x := by linarith
    rw [abs_of_nonneg hx]
  · --
    rw [abs_of_pos h]
    have hx : -x < 0 := by linarith
    rw [abs_of_neg hx, neg_neg]


example : |x * y| = |x| * |y| := abs_mul x y

theorem t3 (x y : ℝ): |x * y| = |x| * |y| := by
  obtain hx | hx | hx := lt_trichotomy x 0
  · obtain hy | hy | hy := lt_trichotomy y 0
    · --
      rw [abs_of_neg hx];
      rw [abs_of_neg hy];
      rw [abs_of_pos];
      ring
      exact mul_pos_of_neg_of_neg hx hy

    · rw [hy]
      simp

    · --
      rw [abs_of_neg hx];
      rw [abs_of_pos hy];
      rw [abs_of_neg];
      linarith
      exact mul_neg_of_neg_of_pos hx hy

  · rw [hx]
    simp
  · obtain hy | hy | hy := lt_trichotomy y 0
    · rw [abs_of_pos hx];
      rw [abs_of_neg hy];
      rw [abs_of_neg];
      ring
      exact mul_neg_of_pos_of_neg hx hy

    · rw [hy]; simp
    · rw [abs_of_pos hx];
      rw [abs_of_pos hy];
      rw [abs_of_pos];
      positivity


lemma l4  (x : ℝ) : |x * x| = x * x := by
  rw [t3]
  obtain h | h | h := lt_trichotomy x 0
  · repeat rw [abs_of_neg]
    ring; exact h
  · rw [h]; simp
  · repeat rw [abs_of_pos]; exact h

theorem t4 : |x ^ 2| = x ^ 2 ∧ x ^ 2 = |x| ^ 2 := by
  rw [pow_two x, pow_two |x|]
  constructor
  · apply l4
  · -- reuse l4
    rw [←t3]
    symm
    apply l4

theorem t5' : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y := by
  obtain h | h := le_or_lt x 0
  constructor
  · intro h₁
    constructor
    · rw [abs_of_nonpos h] at h₁
      linarith
    · rw [abs_of_nonpos h] at h₁
      linarith
  · intro ⟨h₁, h₂⟩
    rw [abs_of_nonpos h]
    linarith
  constructor
  · intro h₁
    rw [abs_of_pos h] at h₁
    constructor
    · linarith
    · linarith
  · intro ⟨h₁, h₂⟩
    rw [abs_of_pos h]
    exact h₂

theorem t6 : x ≤ |x| := by
  obtain h | h := le_or_lt x 0
  · rw [abs_of_nonpos h]
    linarith
  · rw [abs_of_pos h]

example : |x * y| ≤ |x| * |y| := by
  rw [le_iff_lt_or_eq]
  right
  apply t3

example : |x * y| ≤ |x| * |y| := by
  rw [le_iff_lt_or_eq]
  right
  apply t3

example (x y : ℝ) : |x - y| = |y - x| := by
  obtain h | h | h := lt_trichotomy (x - y) 0
  · have h₁ : 0 ≤ y - x := by linarith
    rw [abs_of_nonneg h₁, abs_of_neg h]
    linarith
  · have : y - x = 0 := by linarith
    rw [h, this]

  · rw [abs_of_nonneg, abs_of_neg]
    ring
    linarith
    linarith

end abs_koan

end Lecture5
