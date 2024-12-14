import Mathlib

import Pb100.Rec02Util

set_option autoImplicit false

namespace rec_2

-- comments that start with † are remixed from 18.100A, please see LICENSE for
-- more details.

section p2

def X := {a : ℝ | 0 < a ∧ a ^ 3 < 2 }

lemma one_le_r_of_lub (r : ℝ) (h₀ : IsLUB X r) : 1 ≤ r := by
  have ⟨h₁, _⟩ := h₀
  dsimp [IsLUB, X, upperBounds] at h₁
  apply h₁
  aesop

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


theorem find_good_ε (r : ℝ) (h₀ : IsLUB X r) (hc : 2 < r ^ 3) (hr₁ : 0 < r) (hr₂ : 1 < r) :
  ∃ ε, 0 < ε ∧ 2 ≤ r ^ 3 - 3 * r ^ 2 * ε := by
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


lemma step21 (r : ℝ) (h₀ : IsLUB X r) : r ^ 3 ≤ 2 := by
  -- † Assume for the sake of contradiction that 2 < r ^ 3.

  by_contra hc
  push_neg at hc

  -- prepare some facts to help show the contradiciton.

  have hr₁ : 1 < r := by apply one_lt_of_one_lt_cube r; linarith
  have hr₂ : 0 < r := by linarith

  -- † Let’s try to intuitively understand why this should give a contradiction.
  -- Given this is the case, then we should be able to subtract a "small" ε > 0
  -- from r such that 2 < (r − ε) ^ 3, then r − ε is still an upper bound for X.
  -- This would be a contradiction, as the supremum is the least upper bound.
  -- However, we still need to make this proof more formal by explicitly saying
  -- what h is. to do this, consider the following:

  obtain ⟨ε, ⟨hh₀, hh⟩⟩ := find_good_ε r h₀ hc hr₂ hr₁

  -- † notice that if we can find an ε such that 0 < r ^ 3 - 3 * r ^ 2 * ε then
  -- we will have 2 < (r - ε) ^ 3, which would be a contradiction

  let cubic_tail := 3 * r * ε ^ 2 - ε ^ 3
  -- hc : 2 < r ^ 3
  have contra : 2 < (r - ε) ^ 3 :=
    calc 2
      _≤ r ^ 3 - 3 * r ^ 2 * ε := hh
      _= r ^ 3 - 3 * r ^ 2 * ε + (0) := by ring
      _< r ^ 3 - 3 * r ^ 2 * ε + cubic_tail := by
        have : 0 < cubic_tail := by simp [cubic_tail]; nlinarith
        gcongr
      _= (r - ε) ^ 3 := by ring

  -- now we have an element (r - ε) in the upper bounds of X that is less than the
  -- supremum r.

  have h₀' : r - ε ∈ upperBounds X ∧ r - ε < r := by
    constructor
    · dsimp [upperBounds]
      intro p ⟨hp₁, hp₂⟩
      have :=
      calc p ^ 3
        _< 2 := hp₂
        _< (r - ε) ^ 3 := contra
      have this₀ : 0 < p^3 := by positivity
      have this₁ := lt_of_zero_cube_lt_cube p (r-ε) this this₀
      rw [le_iff_lt_or_eq]
      left
      exact this₁
    · linarith

  -- build the contradiction.

  have ⟨hs₁, hcon₁⟩ := h₀'
  have ⟨_, h₂'⟩ := h₀
  have hs₃ := @h₂' (r - ε) hs₁
  have hcon₂ : ¬ (r - ε) < r := by linarith

  contradiction


lemma asdfasdf (r : ℝ) (h₀ : IsLUB X r) : 1 < r := by
  obtain ⟨h₁, _⟩ := h₀
  dsimp [upperBounds] at h₁
  have hx : (10/9) ∈ X := by
    simp [X]
    norm_num
  have h := @h₁ (10/9) hx
  nlinarith

theorem find_good_ε₂ (r : ℝ) (h₀ : IsLUB X r) (hc : r ^ 3 < 2)
    : ∃ ε, 0 < ε ∧ (r + ε) ^ 3 < 2 := by
  --
  let k := 10 -- α ∝ 1 / k
  let ω := 2 - r ^ 3
  let α := ω / (k * r ^ 2)
  use α

  have hr₁ : 1 < r := asdfasdf r h₀
  have hr₂ : 0 < r := by linarith
  have hω  : 0 < ω := by dsimp [ω]; linarith
  have ok₁ : 0 < α := by dsimp [α]; aesop
  have ok₃ : r ≠ 0 := by linarith

  constructor
  · exact ok₁
  · -- (r + α) ^ 3 < 2

    have need₁ : α < r := by
      dsimp [α, ω]
      have : 0 < (10 * r ^ 2) := by aesop
      rw [div_lt_iff₀ this]
      nlinarith

    have piece₁ : 3 * (r * α ^ 2) < 3 * (r ^ 2 * α) := by
      -- clean up with calc block?
      calc 3 * (r * α ^ 2)
        _= 3 * (r * α * α) := by ring
        _< 3 * (r * r * α) := by rel [need₁]
        _= 3 * (r ^2 * α) := by ring

    have piece₂ : α ^ 3 < 3 * r ^ 2 * α := by
      calc α ^ 3
        _= α * α * α := by ring
        _< r * r * α := by rel [need₁]
        _= 1 * r ^ 2 * α := by ring
        _< 3 * r ^ 2 * α := by
          have : 1 < (3:ℝ) := by norm_num
          rel [this]

    have trip :=
      calc 3 * r ^ 2 * α + 3 * r * α ^ 2 + α ^ 3
        _< 3 * r ^ 2 * α + 3 * r ^ 2 * α + 3 * r ^ 2 * α := by linarith
        _= 9 * r ^ 2 * α := by ring

    have final : 9 * r ^ 2 * α < 2 - r ^ 3 := by
      calc 9 * r ^ 2 * α
        _= 9 * r ^ 2 * ω / (k * r ^ 2) := by ring
        _= 9 * r ^ 2 * ω / k * 1 / r ^ 2 := by ring
        _= 9 * r ^ 2 * (1 / r ^ 2) * ω / k  := by ring
        _= 9 * (r ^ 2 / r ^ 2) * ω / k  := by ring
        _= 9 * (1) * ω / k  := by aesop
        _= 9 * ω / 10  := by ring
        _= (9 / 10) * ω := by ring
        _= (9 / 10) * (2 - r ^ 3) := by ring
        _< 1 * (2 - r ^ 3) := by
          have : (9:ℝ) / 10 < 1 := by linarith
          rel [this]
        _= 2 - r ^ 3 := by ring

    calc (r + α) ^ 3
      _= r ^ 3 + (3 * r ^ 2 * α + 3 * r * α ^ 2 + α ^ 3) := by ring
      _< r ^ 3 + (9 * r ^ 2 * α) := by rel [trip]
      _< 2 := by linarith


-- def X := {a : ℝ | 0 < a ∧ a ^ 3 < 2 }
theorem step22 (r : ℝ) (h₀ : IsLUB X r) : 2 ≤ r ^ 3 := by
   -- Assume for the sake of contradiction that r ^ 3 < 2.
  by_contra hc
  push_neg at hc
  have ⟨h₁, h₂⟩ := h₀

  obtain ⟨ε, ⟨hε₁, hε₂⟩⟩ := find_good_ε₂ r h₀ hc

  -- now we have an element (sup + ε) in the Set X but is greater than the
  -- sup r?
  have hr : 0 < r := by
    have := asdfasdf r h₀
    linarith

  have h₀' : r + ε ∈ X ∧ r + ε ∈ upperBounds X := by
    constructor
    · -- intro p ⟨hp₁, hp₂⟩
      simp [Set.mem_def, X]
      constructor
      · -- 0 < r + ε
        linarith
      · exact hε₂
    · -- r + ε ∈ upperBounds X
      exact r_add_ε_in_ub ε r X hε₁ h₀.left

  have := @h₁ (r + ε) h₀'.left
  have con : ¬ (r + ε ≤ r) := by linarith

  contradiction

-- Show that the set X has supremum (sup X)^3 = 2
theorem part2 (r : ℝ) : IsLUB X r → r ^ 3 = 2 := by
  intro h
  rw [le_antisymm_iff]
  refine ⟨step21 r h, step22 r h ⟩

end p2

end rec_2
