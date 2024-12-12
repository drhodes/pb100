import Mathlib
set_option autoImplicit false

namespace rec_2

-- comments that start with † is remixed from 18.100A, please see LICENSE for
-- more details.

section p2

@[reducible]
def bdd (s : Set ℝ) := BddBelow s ∧ BddAbove s

def X := {a : ℝ | 0 < a ∧ a ^ 3 < 2 }

lemma lem₁ {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a < b ↔ a ^ c < b ^ c := by
  refine Iff.symm (Real.rpow_lt_rpow_iff ?_ ?_ hc)
  exact le_of_lt ha
  exact le_of_lt hb

lemma lem2 (a b : ℝ) (h : 0 ≤ a) : a ^ (b⁻¹ * b) = (a ^ b⁻¹) ^ b  := by
  exact Real.rpow_mul h b⁻¹ b

-- † Step 1. Show that the set X is bounded, which then implies it must have a
-- supremum as a property of the real

lemma part1 : bdd X := by
  constructor
  · -- r ^ 3 ≤ 2
    use -1
    intro a ⟨ha₁, _⟩
    linarith

  · -- 2 ≤ r ^ 3
    use 3
    intro a ⟨ha₁, ha₂⟩

    rw [le_iff_lt_or_eq]
    left

    -- what about generalization of trichotomy

    -- trichotomy helps decompose the argument into three "proof-domains"
    -- partioning the proof where the variable `a` is, in this case
    -- a < 1, a = 1, 1 < a

    obtain h | h | h := (lt_trichotomy 1 a)
    · calc a
        _= a * 1 := by ring
        _< a * a := by rel [h]
        _= a * a * 1 := by ring
        _< a * a * a := by rel [h]
        _= a ^ 3 := by ring
        _< 2 := ha₂
        _< 3 := by norm_num
    · linarith
    · linarith


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

theorem support_for_two (r : ℝ) (h₀ : IsLUB X r) (hc : 2 < r ^ 3) (hr₁ : 0 < r) (hr₂ : 1 < r) :
  ∃ h, 0 < h ∧ 2 ≤ r ^ 3 - 3 * r ^ 2 * h := by
  --
  have ⟨h₁, h₂⟩ := h₀
  use (r ^ 3 - 2) / (3 * r ^ 2)
  constructor
  · aesop
  · --
    rw [bs_mul_le r]
    rw [bs_mul_le (1/2)]
    conv => lhs; simp; rw [mul_comm, mul_assoc]; simp
    apply h₂
    intro b ⟨hb₁, hb₂⟩

    have h₃ :=
      calc b ^ 3
        _< 2 := hb₂
        _< r ^ 3 := hc

    have har : b ≤ r := by apply h₁; refine ⟨hb₁, hb₂⟩

    let p := r^3
    let q := r^2

    have hq₀ : 3 * q ≠ 0 := by aesop
    have hr2 : 1 = (3 * q) / (3 * q) := by rw [div_self hq₀]

    have h₅ :=
      calc b
        _≤ r := har
        _= (1 / 2) * r * 2 := by ring
        _= (1 / 2) * (r * (p - p + 2)) := by ring
        _= (1 / 2) * (r * (p - (p - 2))) := by ring
        _= (1 / 2) * (r * (p - (        1        ) * (p - 2))) := by ring
        _= (1 / 2) * (r * (p - ((3 * q) / (3 * q)) * (p - 2))) := by rw [hr2]
        _= (1 / 2) * (r * (p - 3 * q * (1 / (3 * q)) * (p - 2))) := by ring
        _= (1 / 2) * (r * (p - 3 * q * (p - 2) * (1 / (3 * q)))) := by ring
        _= (1 / 2) * (r * (p - 3 * q * (p - 2) / (3 * q))) := by ring
        _= (1 / 2) * (r * (r ^ 3 - 3 * r ^ 2 * (r ^ 3 - 2) / (3 * r ^ 2))) := by ring
        _= (1 / 2) * (r * (r ^ 3 - 3 * r ^ 2 * ((r ^ 3 - 2) / (3 * r ^ 2)))) := by ring

    exact h₅
    norm_num
    exact hr₁

theorem step21 (r : ℝ) (h₀ : IsLUB X r) : r ^ 3 ≤ 2 := by
  -- † Assume for the sake of contradiction that 2 < r ^ 3.

  have ⟨h₁, h₂⟩ := h₀
  by_contra hc
  push_neg at hc

  -- † Let’s try to intuitively understand why this should give a contradiction.
  -- Given this is the case, then we should be able to subtract a "small" h > 0
  -- from r such that 2 < (r − h) ^ 3, then r − h is still an upper bound for X.
  -- This would be a contradiction, as the supremum is the least upper bound.
  -- However, we still need to make this proof more formal by explicitly saying
  -- what h is. to do this, consider the following:

  dsimp [lowerBounds, upperBounds, X] at h₁ h₂

  have hr₂ : 1 < r := by
    have :=
      calc 1
        _< (2:ℝ) := by norm_num
        _< r^3 := hc
    apply one_lt_of_one_lt_cube r this

  have hr₁ : 0 < r := by linarith

  --
  obtain ⟨h, ⟨hh₀, hh⟩⟩ := support_for_two r h₀ hc hr₁ hr₂

  have hh₃ : h < r / 3 := by
    have h2 :=
    calc 2
      _≤ r ^ 3 - 3 * r ^ 2 * h := hh
      _= r ^ 2 * (r - 3 * h) := by ring
    have h3 : 0 < r - 3 * h := by nlinarith
    linarith

  have hh₄ : 0 < 3 * r * h ^ 2 - h ^ 3 := by nlinarith

  -- † notice that if we can find an h such that 2 ≤ r ^ 3 - 3 * r ^ 2 * h then
  -- we will have 2 < (r - h) ^ 3, which would be a contradiction

  have contra : 2 < (r - h) ^ 3 :=
    calc 2
      _≤ r ^ 3 - 3 * r ^ 2 * h := hh
      _= r ^ 3 - 3 * r ^ 2 * h + (0) := by ring
      _< r ^ 3 - 3 * r ^ 2 * h + (3 * r * h ^ 2 - h ^ 3) := by rel [hh₄]
      _= (r - h) ^ 3 := by ring

  -- now we have an element (r - h) in the upper bounds of X that is less than the
  -- supremum r.

  have h₀' : ∃ p, p ∈ upperBounds X ∧ p < r := by
    use r - h
    constructor
    · dsimp [upperBounds]
      intro p ⟨hp₁, hp₂⟩
      have :=
      calc p ^ 3
        _< 2 := hp₂
        _< (r - h) ^ 3 := contra
      have this₀ : 0 < p^3 := by positivity
      have this₁ := lt_of_zero_cube_lt_cube p (r-h) this this₀
      rw [le_iff_lt_or_eq]
      left
      exact this₁
    · linarith

  --
  have ⟨s, ⟨hs₁, hs₂⟩⟩ := h₀'
  have ⟨_, h₂'⟩ := h₀
  have hs₃ := @h₂' s hs₁
  have : ¬ s < r := by linarith
  contradiction


theorem step22 (r : ℝ) (h₀ : IsLUB X r) : 2 ≤ r ^ 3 := by
  have ⟨h₁, h₂⟩ := h₀
  sorry

lemma part2 (r : ℝ) : IsLUB X r → r ^ 3 = 2 := by
  intro h
  rw [le_antisymm_iff]
  refine ⟨step21 r h, step22 r h⟩

end p2

end rec_2
