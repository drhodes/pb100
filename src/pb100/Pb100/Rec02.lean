import Mathlib
set_option autoImplicit false

namespace rec_2

-- note, need to determine if this course can be done without having to rely on
-- roots at all.

section p2

@[reducible]
def bdd (s : Set ℝ) := BddBelow s ∧ BddAbove s

def X := {a : ℝ | 0 < a ∧ a ^ 3 < 2 }

-- example (a : ℝ) : IsLeast X = ⊥ := by
--   exact?

--   sorry
--bot_le : ∀ (a : α), ⊥ ≤ a

-- Step 1. Show that the set X is bounded, which them implies it must have a
-- supremum as a property of the real

lemma lem₁ {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a < b ↔ a ^ c < b ^ c := by
  refine Iff.symm (Real.rpow_lt_rpow_iff ?_ ?_ hc)
  exact le_of_lt ha
  exact le_of_lt hb


lemma lem2 (a b : ℝ) (h : 0 ≤ a) : a ^ (b⁻¹ * b) = (a ^ b⁻¹) ^ b  := by
  exact Real.rpow_mul h b⁻¹ b

lemma step1 : bdd X := by
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

lemma lt_cube_of_lt (r : ℝ) (hr : 0 < r ^ 3) : 0 < r := by
  have : Odd 3 := by exact Nat.odd_iff.mpr rfl
  exact (Odd.pow_pos_iff this).mp hr

lemma lt_cube_of_one_lt (r : ℝ) (hr : 1 < r ^ 3) : 1 < r := by
  have : Odd 3 := by exact Nat.odd_iff.mpr rfl
  have rsqpos : 0 ≤ r * r := by exact mul_self_nonneg r
  have lt_cube := lt_cube_of_lt r ?_
  nlinarith
  nlinarith

example : IsLeast {x : ℕ | 0 ≤ x} 0 := by
  constructor
  · norm_num
  · --
    dsimp [lowerBounds]
    intro a ha
    exact ha

example : IsLeast (Set.univ : Set ℕ) 0 :=
  ⟨Set.mem_univ 0, λ a _ => Nat.zero_le a ⟩

example : IsLeast (Set.univ : Set ℕ) 0 := by aesop

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

    exact h₅
    norm_num
    exact hr₁


theorem step21 (r : ℝ) (h₀ : IsLUB X r) : r ^ 3 ≤ 2 := by
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

  have hr₁ : 0 < r := by
    have : Odd 3 := by exact Nat.odd_iff.mpr rfl
    have hc₂ :=
      calc 0 < (2:ℝ) := by norm_num
        _< r ^ (3:ℕ) := hc
    exact (Odd.pow_pos_iff this).mp hc₂

  have hr₂ : 1 < r := by
    have :=
      calc 1
        _< (2:ℝ) := by norm_num
        _< r^3 := hc
    apply lt_cube_of_one_lt r this

  --
  obtain ⟨h, ⟨hh₀, hh⟩⟩ := support_for_two r h₀ hc hr₁ hr₂

  have hh₃ : h < r / 3 := by
    have h2 :=
    calc 2
      _≤ r ^ 3 - 3 * r ^ 2 * h := hh
      _= r ^ 2 * (r - 3 * h) := by ring
    have h3 : 0 < r - 3 * h := by nlinarith
    linarith

  -- have hh₄ : h ^ 2 < r ^ 2 := by
  --   calc h ^ 2
  --     _< (r/3)^2 := by rel [hh₃]


  -- notice that if we can find an h such that 2 ≤ r ^ 3 - 3 * r ^ 2 * h then we
  -- will have 2 < (r - h) ^ 3, which would be a contradiction

  have test : 2 < (r - h) ^ 3 :=
    have part₃ :=
      calc r ^ 3 - 3 * r * h ^ 2
        _> r ^ 3 - 3 * r * (r / 3) ^ 2 := by rel [hh₃]
        _> r ^ 3 - 3 * r * r ^ 2 := by linarith
        _= r ^ 3 - 3 * r ^ 3 := by ring
        _= - 2 * r ^ 3 := by ring

    by calc 2
        _ ≤ r ^ 3 - 3 * r ^ 2 * h := hh
        _ = r ^ 3 - 3 * r ^ 2 * h + 0 := by ring
        _ < r ^ 3 - 3 * r ^ 2 * h + 3 * r * h ^ 2 - r ^ 3 / 27  := by linarith
        = < r ^ 3 - 3 * r ^ 2 * h + 3 * r * h ^ 2 - h ^ 3  := by ring
        _ = (r - h) ^ 3 := by ring

  have h₀' : IsLUB X (r - h) := by
    · sorry
    · sorry


  have h00 : r ≠ r - h := by linarith

  apply both_not_least r (r-h) (upperBounds X) h00

  simp_all only [and_imp, ne_eq]
  apply And.intro
  · exact h₀
  · exact h₀'


theorem step22 (r : ℝ) (h₀ : IsLUB X r) : 2 ≤ r ^ 3 := by
  have ⟨h₁, h₂⟩ := h₀
  sorry

lemma step2 (r : ℝ) : IsLUB X r → r ^ 3 = 2 := by
  intro h
  rw [le_antisymm_iff]
  refine ⟨step21 r h, step22 r h⟩

end p2

end rec_2
