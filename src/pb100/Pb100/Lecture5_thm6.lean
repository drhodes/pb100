import Mathlib

import Pb100.Lecture5Util
import Pb100.Lecture5_thm4

namespace Lecture5

open Set

namespace thm_6



-- Lecture 5, Theorem 6
-- part 1. If x ∈ ℝ, sup(x + A) = x + sup A.

theorem part1_mine
  (x supa supx : ℝ) (A X : Set ℝ)
  (hxa : X = {x + a | a ∈ A})
  (ha : IsLUB A supa)
  (hx : IsLUB X supx) : supx = supa + x := by
  --
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hx₁, hx₂⟩ := hx
  rw [le_antisymm_iff]

  constructor
  · --
    apply hx₂
    intro d hd
    rw [← tsub_le_iff_right]
    apply ha₁
    rw [hxa] at hd
    obtain ⟨j, hj₁, hj₂⟩ := hd
    rw [← hj₂]
    simpa
  · --
    rw [← le_sub_iff_add_le]
    apply ha₂
    intro d hd
    rw [le_sub_iff_add_le]
    apply hx₁
    rw [hxa]
    use d
    refine ⟨hd, by linarith⟩


theorem part2_mine
  (x supa supx : ℝ) (A X : Set ℝ)
  (hx : 0 < x)
  (hxa : X = {x * a | a ∈ A})
  (ha : IsLUB A supa)
  (hx : IsLUB X supx) : supx = supa * x := by
  --
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hx₁, hx₂⟩ := hx
  rw [le_antisymm_iff]

  constructor
  · --
    apply hx₂
    intro d hd
    rw [Iff.symm (div_le_iff₀ hx)]
    apply ha₁
    rw [hxa] at hd
    obtain ⟨j, hj₁, hj₂⟩ := hd
    rw [← hj₂]
    field_simp
    assumption
  · --
    rw [Iff.symm (le_div_iff₀ hx)]
    apply ha₂
    intro d hd
    rw [← Iff.symm (le_div_iff₀ hx)]
    apply hx₁
    rw [hxa]
    use d
    refine ⟨hd, by linarith⟩


-- part 2. If x ∈ ℝ and 0 < x : sup(x ⬝ A) = x · sup A.

-- TODO redo this proof as the course intended with ε
/-
theorem Lecture5.thm_6.extracted_1 (ε x supa supx : ℝ) (A X : Set ℝ) (he : A.Nonempty) (hba : BddAbove A)
  (hxa : X = {x_1 | ∃ a ∈ A, x * a = x_1}) (h₀ : 0 < x) (hε : 0 < ε) (ha : IsLUB A supa) (hx : IsLUB X supx)
  (hs₀ : ∀ a ∈ A, a ≤ supa) (hs₁ : ∀ a ∈ A, x * a ≤ x * supa) (hs₂ : x * supa ∈ upperBounds X)
  (hs₃ : ∃ y ∈ A, supa - ε / x < y ∧ y ≤ supa → x * supa - ε < x * y ∧ x * y ≤ x * supa) : supx = x * supa := by
  --
  have thm4 := Lecture5.thm_4.theorem_4 x A hba he
  obtain ⟨y, hy₁, hy₂⟩ := hs₃
  have ⟨ha₁, ha₂⟩ := ha


theorem part2
  (ε x supa supx : ℝ) (A X : Set ℝ)
  (he : A.Nonempty)
  (hba : BddAbove A)
  (hxa : X = {x * a | a ∈ A})
  (h₀ : 0 < x)
  (hε : 0 < ε)
  (ha : IsLUB A supa)
  (hx : IsLUB X supx) :
    BddAbove X ∧ supx = x * supa := by
  --
  suffices hs₀ : ∀ a ∈ A, a ≤ supa
  suffices hs₁ : ∀ a ∈ A, x * a ≤ x * supa
  suffices hs₂ : x * supa ∈ upperBounds X
  suffices hs₃ : ∃ y ∈ A, supa - ε / x < y ∧ y ≤ supa →
                          x * supa - ε < x * y ∧ x * y ≤ x * supa

  constructor
  · exact nonempty_of_mem hs₂
  · exact Lecture5.thm_6.extracted_1 ε x supa supx A X he hba hxa h₀ hε ha hx hs₀ hs₁ hs₂ hs₃

-/
end thm_6

end Lecture5
