import Mathlib
set_option autoImplicit false

namespace rec_2

section p2


@[reducible]
def bdd (s : Set ℝ) := BddBelow s ∧ BddAbove s

def X := {a : ℝ | 0 < a ∧ a ^ (3:ℝ) < 2 }

-- Step 1. Show that the set X is bounded, which them implies it must have a
-- supremum as a property of the real


lemma lem₁ {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a < b ↔ a ^ c < b ^ c := by
  refine Iff.symm (Real.rpow_lt_rpow_iff ?_ ?_ hc)
  exact le_of_lt ha
  exact le_of_lt hb

lemma lem2 (a b : ℝ) (h : 0 ≤ a) : a ^ (b⁻¹ * b) = (a ^ b⁻¹) ^ b  := by
  exact Real.rpow_mul h b⁻¹ b

-- this is kind of awful.
lemma step1 : bdd X := by
  constructor
  · -- r ^ 3 ≤ 2
    use -1
    intro a ⟨ha₁, _⟩
    linarith

  · -- 2 ≤ r ^ 3
    let p := (3:ℝ)⁻¹
    let m := (2:ℝ) ^ p
    use m
    intro a ⟨ha₁, ha₂⟩

    rw [le_iff_lt_or_eq]
    left

    have h2 : 0 ≤ (2:ℝ) := by norm_num
    have h4 := lem2 2 3 h2
    have h3 : p * 3 = 1 := by linear_combination
    rw [h3] at h4
    norm_num at h4

    have temp₁ : 0 < a := by positivity
    have temp₂ : 0 < m := by positivity
    have temp₃ : 0 < (3:ℝ) := by norm_num
    rw [lem₁ temp₁ temp₂ temp₃]

    have one_third_is_three_inv : 1 / 3 = (3 : ℝ)⁻¹ := by exact one_div 3
    rw [one_third_is_three_inv] at h4
    rw [←h4]
    exact ha₂


lemma bs_mul_le {a b : ℝ} (c : ℝ) (hc : 0 < c): a ≤ b ↔ c * a ≤ c * b := by
  exact Iff.symm (mul_le_mul_iff_of_pos_left hc)

lemma bs_mul_lt {a b : ℝ} (c : ℝ) (hc : 0 < c): a < b ↔ c * a < c * b := by
  exact Iff.symm (mul_lt_mul_iff_of_pos_left hc)

lemma mul_one_rhs {a b : ℝ} : a ≤ b ↔ a ≤ 1 * b := by ring_nf

lemma both_not_least (a b : ℝ) (X: Set ℝ) (h : a ≠ b) : ¬ (IsLeast X a ∧ IsLeast X b) := by
  intro ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩
  have hc₁ := @hb₂ a ha₁
  have hc₂ := @ha₂ b hb₁
  have : a = b := by linarith
  contradiction


theorem step21 (r : ℝ) (h₀ : IsLUB X r) : r ^ (3:ℝ) ≤ 2 := by
  -- Assume for the sake of contradiction that 2 < r ^ 3.
  have ⟨h₁, h₂⟩ := h₀
  by_contra hc
  push_neg at hc

  -- Let’s try to intuitively understand why this should give a contradiction.
  -- Given this is the case, then we should be able to subtract a "small" h > 0
  -- from r such that 2 < (r − h) ^ 3, then r − h is still an upper bound for
  -- X. This would be a contradiction, as the supremum is the least upper bound.
  -- However, we still need to make this proof more formal by explicitly saying
  -- what h is. to do this, consider the following:


  dsimp [lowerBounds, upperBounds, X] at h₁ h₂

  have hh : ∃ h, 2 ≤ r ^ 3 - 3 * r ^ 2 * h := by
    use (r^3 - 2)/(3*r^2)
    --field_simp
    rw [bs_mul_le r]
    rw [bs_mul_le (1/2)]
    conv => lhs; simp; rw [mul_comm, mul_assoc]; simp
    apply h₂
    intro a ⟨ha₁, ha₂⟩
    have h₃ :=
      calc a ^ 3
        _< 2 := ha₂
        _< r ^ 3 := hc

    have hl₂ : 0 < r := by
      have :=
      calc (0:ℝ)
        _< 2 := by norm_num
        _< r ^ 3 := hc



    have hl₃ : 0 < (3:ℝ) := by norm_num
    rw [← lem₁ ha₁ hl₂ hl₃] at h₃

    let p := r^3
    let q := r^2

    have hr2 : 1 = (3*q)/(3*q) := by
      rw [div_self]
      intro h
      have hr₁ : 1 < r := by sorry
      have hr₂
      calc 0
        _< r := hl₂
        _< 3 * r := by linarith
        _= 3 * r * 1 := by ring
        _< 3 * r * r := by rel [hr₁]
        _= 3 * r^2 := by ring
        _= 0 := h
      norm_num at hr₂

    have h₅ :=
      calc a
        _< r := h₃
        _= (1/2) * r * 2 := by ring
        _= (1/2) * (r * (p - p + 2)) := by ring
        _= (1/2) * (r * (p - (p - 2))) := by ring
        _= (1/2) * (r * (p - (     1     ) * (p - 2))) := by ring
        _= (1/2) * (r * (p - ((3*q)/(3*q)) * (p - 2))) := by conv => lhs; rhs; rhs; rhs; lhs; rw [hr2]
        _= (1/2) * (r * (p - 3*q * (1/(3*q)) * (p - 2))) := by ring
        _= (1/2) * (r * (p - 3*q * (p - 2) * (1/(3*q)))) := by ring
        _= (1/2) * (r * (p - 3*q * ((p - 2)/(3*q)))) := by ring
        _= 1 / 2 * (r * (r ^ 3 - 3 * r ^ 2 * (r ^ 3 - 2) / (3 * r ^ 2))) := by ring
        _= 1 / 2 * (r * (r ^ 3 - 3 * r ^ 2 * ((r ^ 3 - 2) / (3 * r ^ 2)))) := by ring

    exact le_of_lt h₅
    norm_num
    have hr10 :=
      calc (0:ℝ)
        _< 2 := by norm_num
        _< r ^ 3 := hc
    -- lemma bs_mul_lt {a b : ℝ} (c : ℝ) (hc : 0 < c): a < b ↔ c * a < c * b := by

    rw [cancel_club] at hr10

    sorry

  have hr₆ := @h₁ 1 -- Note: maybe instead of 1 this could be something smaller?
  norm_num at hr₆
  have hr₇ := @h₁ (1/8) -- Note: maybe instead of 1 this could be something smaller?
  norm_num at hr₇
  have hr₈ : 2 ≤ 2 * r := by linarith

  obtain ⟨h, hh⟩ := hh

  have : 0 < h := by sorry
  have : h < r := by sorry

  -- notice that if we can find an h such that 2 ≤ r ^ 3 - 3 * r ^ 2 * h then we
  -- will have 2 < (r - h) ^ 3, which would be a contradiction
  have h₀' : IsLUB X (r - h) := by
    constructor
    · dsimp [upperBounds]
      intro b hb
      have hb₁ := @h₁ (b + h)
      have : b ≤ r - h ↔ b + h ≤ r := by exact le_sub_iff_add_le
      rw [this]
      apply hb₁
      obtain ⟨b₁, b₂⟩ := hb
      constructor
      · linarith
      · sorry
    · --
      dsimp [lowerBounds, upperBounds]
      intro b hb
      apply hb
      sorry


  have h00 : r ≠ r - h := by linarith

  apply both_not_least r (r-h) (upperBounds X) h00

  simp_all only [and_imp, ne_eq]
  apply And.intro
  · exact h₀
  · exact h₀'


theorem step22 (r : ℝ) (h₀ : IsLUB X r) : 2 ≤ r ^ (3:ℝ) := by
  have ⟨h₁, h₂⟩ := h₀
  sorry

lemma step2 (r : ℝ) : IsLUB X r → r^(3:ℝ) = 2 := by
  intro h₀

  rw [le_antisymm_iff]
  constructor
  · apply step21 r h₀
  · apply step22 r h₀

end p2

end rec_2
