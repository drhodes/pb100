import Mathlib
set_option autoImplicit false

namespace rec_2

@[reducible]
def bdd (s : Set ℝ) := BddBelow s ∧ BddAbove s

lemma r_add_ε_in_ub (ε r : ℝ) (X : Set ℝ) (hε : 0 < ε)
  (hr : r ∈ upperBounds X) : r + ε ∈ upperBounds X := by
  --
  intro x h₂
  dsimp [upperBounds] at hr
  have hx := @hr x h₂
  linarith


lemma bs_mul_le {a b : ℝ} (c : ℝ) (hc : 0 < c): a ≤ b ↔ c * a ≤ c * b := by
  exact Iff.symm (mul_le_mul_iff_of_pos_left hc)

lemma bs_mul_lt {a b : ℝ} (c : ℝ) (hc : 0 < c): a < b ↔ c * a < c * b := by
  exact Iff.symm (mul_lt_mul_iff_of_pos_left hc)

lemma mul_one_rhs {a b : ℝ} : a ≤ b ↔ a ≤ 1 * b := by ring_nf

lemma both_not_least (a b : ℝ) (X: Set ℝ) (h : a ≠ b) : (IsLeast X a ∧ IsLeast X b) → False := by
  intro ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩
  have hc₁ := @hb₂ a ha₁
  have hc₂ := @ha₂ b hb₁
  have : a = b := by linarith
  contradiction

lemma zero_lt_of_lt_cube (r : ℝ) (hr : 0 < r ^ 3) : 0 < r := by
  have : Odd 3 := by exact Nat.odd_iff.mpr rfl
  exact (Odd.pow_pos_iff this).mp hr

lemma cube_lt_cube_of_lt (a b : ℝ) (ha₁ : a < b) (ha₂ : 0 < a) : a ^ 3 < b ^ 3 := by
  have : 0 < b := by exact gt_trans ha₁ ha₂
  have : 0 < a ^ 3 := by positivity
  have : 0 < b ^ 3 := by positivity
  calc a^3
    _= a * a * a := by ring
    _< b * b * b := by rel [ha₁]
    _= b ^ 3 := by ring

lemma lt_of_one_cube_lt_cube (a b : ℝ) (ha₁ : a ^ 3 < b ^ 3) (ha₂ : 1 < a) : a < b := by
  have h₀ : 0 ≤ a := by linarith
  have h₁ : 0 ≤ b := by
    have := calc 0
      _< a := by linarith
      _= a * 1 * 1 := by ring
      _< a * a * a := by rel [ha₂]
      _= a^3 := by ring
      _< b^3 := ha₁
    have hz := zero_lt_of_lt_cube b this
    linarith

  have h₂ : 3 ≠ 0 := by norm_num
  rw [← pow_lt_pow_iff_left h₀ h₁ h₂]
  exact ha₁

lemma lt_of_zero_cube_lt_cube (a b : ℝ) (ha₁ : a ^ 3 < b ^ 3) (ha₂ : 0 < a ^ 3) : a < b := by
  have h₀ : 0 ≤ a := by
    rw [le_iff_lt_or_eq]
    left
    apply zero_lt_of_lt_cube a ha₂

  have h₁ : 0 ≤ b := by
    have := calc 0
      _< a^3 := by linarith
      _< b^3 := ha₁
    have hz := zero_lt_of_lt_cube b this
    linarith

  have h₂ : 3 ≠ 0 := by norm_num
  rw [← pow_lt_pow_iff_left h₀ h₁ h₂]
  exact ha₁

lemma one_lt_of_one_lt_cube (r : ℝ) (hr : 1 < r ^ 3) : 1 < r := by
  have : Odd 3 := by exact Nat.odd_iff.mpr rfl
  have rsqpos : 0 ≤ r * r := by exact mul_self_nonneg r
  have lt_cube := zero_lt_of_lt_cube r ?_
  · nlinarith
  · nlinarith

lemma lt_of_cube_lt {a b: ℝ} (h : a ^ 3 < b) (hb : 1 < b): a < b := by
  obtain h1 | h1 | h1 := lt_trichotomy a 1
  · linarith
  · linarith
  · calc a
      _= a * 1 * 1 := by ring
      _< a * a * a := by rel [h1]
      _= a ^ 3 := by ring
      _< (b:ℝ) := h

lemma le_of_cube_le {a b: ℝ} (h : a ^ 3 ≤ b) (hb : 1 ≤ b): a ≤ b := by
  obtain h1 | h1 | h1 := lt_trichotomy a 1
  · linarith
  · linarith
  · calc a
      _= a * 1 * 1 := by ring
      _≤ a * a * a := by rel [h1]
      _= a ^ 3 := by ring
      _≤ (b:ℝ) := h

lemma r_le_2_of_r_cubed_le_2 (r : ℝ) (h : r ^ 3 ≤ 2) : r ≤ 2 := by
  have := le_of_cube_le h
  norm_num at this
  linarith


lemma zero_lt_r_of_zero_lt_r_cubed (r : ℝ) (h : 0 < r ^ 3) : 0 < r :=
  by exact zero_lt_of_lt_cube r h




end rec_2
