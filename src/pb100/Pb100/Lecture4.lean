import Mathlib

namespace Lecture4

-- page 26,
-- Proposition 1.1.8

variable (F : Type*)
variable [LinearOrderedField F]


-- --theorem a1 If 𝑥 ∈ 𝐹 and 𝑦 ∈ 𝐹, then 𝑥 + 𝑦 ∈ 𝐹.
-- theorem a2 (commutativity of addition) 𝑥 + 𝑦 = 𝑦 + 𝑥 for all 𝑥, 𝑦 ∈ 𝐹.
-- theorem a3 (associativity of addition) (𝑥 + 𝑦) + 𝑧 = 𝑥 + (𝑦 + 𝑧) for all 𝑥, 𝑦, 𝑧 ∈ 𝐹.
-- theorem a4 There exists an element 0 ∈ 𝐹 such that 0 + 𝑥 = 𝑥 for all 𝑥 ∈ 𝐹.
-- theorem a5 For every element 𝑥 ∈ 𝐹, there exists an element −𝑥 ∈ 𝐹 such that 𝑥 + (−𝑥) = 0.
-- theorem a1 If 𝑥 ∈ 𝐹 and 𝑦 ∈ 𝐹, then 𝑥𝑦 ∈ 𝐹.
-- theorem a2 (commutativity of multiplication) 𝑥𝑦 = 𝑦𝑥 for all 𝑥, 𝑦 ∈ 𝐹.
-- theorem a3 (associativity of multiplication) (𝑥𝑦)𝑧 = 𝑥(𝑦𝑧) for all 𝑥, 𝑦, 𝑧 ∈ 𝐹.
-- theorem a4 There exists an element 1 ∈ 𝐹 (and 1 ≠ 0) such that 1𝑥 = 𝑥 for all 𝑥 ∈ 𝐹.
-- theorem a5 For every 𝑥 ∈ 𝐹 such that 𝑥 ≠ 0 there exists an element 1/𝑥 ∈ 𝐹 such that 𝑥(1/𝑥) = 1.
-- theorem d1 (distributive law) 𝑥(𝑦 + 𝑧) = 𝑥𝑦 + 𝑥𝑧 for all 𝑥, 𝑦, 𝑧 ∈ 𝐹


-- ------------------------------------------------------------
section proposition_1_1_8

variable (x y z w : F)

example (h : 0 < x) : -x < 0 := by
  rw [← add_lt_add_iff_left x]
  rw [add_comm]
  rw [neg_add_cancel, add_zero]
  exact h

example : 0 < x → y < z → x * y < x * z := by
  intro h₁ h₂
  rel [h₂]

example : x < 0 → y < z → x * z < x * y := by
  intro h₁ h₂
  field_simp -- todo
  exact h₂

example : x ≠ 0 → 0 < x ∨ x < 0 := by
  intro h
  apply lt_or_gt_of_ne
  symm
  exact h

example : x ≠ 0 → 0 < x ^ 2 := by
  -- rw [le_iff_lt_or_eq] at hc
  intro h
  apply lt_or_gt_of_ne at h
  cases h with
  | inl h => nlinarith -- todo
  | inr h => nlinarith

example (h₁ : 0 < x) (h₂ : x < y) : 0 < 1/y ∧ 1/y < 1/x := by
  constructor
  · field_simp
    linarith
  · --
    exact one_div_lt_one_div_of_lt h₁ h₂ -- todo break this down

example (h₁ : 0 < x) (h₂ : x < y) : x^2 < y^2 := by
  refine sq_lt_sq' ?_ h₂      -- todo clean up.
  refine neg_lt_of_neg_lt ?_
  calc -x
    _< 0 := by linarith
    _< x := by linarith
    _< y := h₂

example (h₁ : x ≤ y) (h₂ : z ≤ w) : x + z ≤ y + w := by
  rel [h₁, h₂]

end proposition_1_1_8


-- ---------------------------------------------------------------
section prop_1_1_9

variable [LinearOrderedField F] (x y : F)

@[reducible]
def same_sign (x y : F) := 0 < x ∧ 0 < y ∨ x < 0 ∧ y < 0

example (h₁ : 0 < x * y) : same_sign x y := by
  sorry

end prop_1_1_9

end Lecture4
