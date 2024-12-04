import Mathlib

namespace Lecture4

section theorem_12

open Set

def E := { x : ℝ | 0 < x ∧ x ^ 2 < 2 }

-- result from lecture 3!

lemma alg₁ (x q : ℝ) (h : x ≠ 0):
  (x - (x ^ 2 - 2) / (2 * x) + q) = ((x ^ 2 + 2) / (2 * x) + q) := by
    have h₁ : 2 * x ≠ 0 := by aesop
    calc (x - (x ^ 2 - 2) / (2 * x) + q)
      _= (x + (2 - x ^ 2) / (2 * x) + q) := by ring
      _= (1 * x + (2 - x ^ 2) / (2 * x) + q) := by ring
      _= (((2 * x) / (2 * x)) * x + (2 - x ^ 2) / (2 * x) + q) := by
        rw [← div_self h₁]
      _= (((2 * x^2) / (2 * x)) + (2 - x ^ 2) / (2 * x) + q) := by ring
      _= ((2 * x^2 + 2 - x ^ 2) / (2 * x) + q) := by ring
      _= ((x ^ 2 + 2) / (2 * x) + q) := by ring

lemma rel₁ (a b : ℝ) {ha : 0 < a} {hab : 0 < a * b} : 0 < b := by
  exact (pos_iff_pos_of_mul_pos hab).mp ha

lemma lubp_part_1 (x : ℝ) : IsLUB E x → x^2 = 2 := by
  --
  intro h₉
  have con₁ := h₉
  dsimp [IsLUB, IsLeast, upperBounds, lowerBounds] at h₉
  obtain ⟨h₁, h₂⟩ := h₉

  -- ⊢ x ^ 2 = 2
  rw [le_antisymm_iff]
  constructor
  · -- x^2 ≤ 2
    have h₃ : ¬ 2 < x^2 := by
      by_contra h₃
      let H := (x ^ 2 - 2) / (2 * x)

      have H₁ : 0 < H := by
        dsimp [H]
        have : 1 ≤ x := by
          apply h₁
          unfold E; norm_num
        rw [div_pos_iff_of_pos_right]
        linarith
        linarith
      have H₂ : x - H < x := by linarith

      have H₃ : upperBounds E (x - H) := by
        simp [upperBounds, E]
        intro q hq₀ hq₁
        have hx : x ≠ 0 := by aesop
        have hx₂ : 2 * x ≠ 0 := by aesop
        have hx₃ : 0 < x := by aesop
        have h₄ :=
          calc (x - H)^2
            _= x^2 - 2*x*H + H^2 := by ring
            _= x^2 - ((2*x) * (x ^ 2 - 2)) / (2 * x) + H^2 := by ring
            _= x^2 - ((x^2 - 2) * (2 * x)) / (2 * x) + H^2 := by ring
            _= x^2 - ((x^2 - 2) * ((2 * x) / (2 * x))) + H^2 := by ring
            _= x^2 - ((x^2 - 2) * (1)) + H^2 := by rw [div_self hx₂]
            _= x^2 - x^2 + 2 + H^2 := by ring
            _= 2 + H^2 := by ring
            _> 2 := by nlinarith

        have h₆ :=
          calc 0
            _< (x-H)^2 - q^2 := by linarith
            _= (x - H + q) * (x - H - q) := by ring
            _= (x - (x ^ 2 - 2) / (2 * x) + q) * (x - H - q) := by ring
            _= ((x ^ 2 + 2) / (2 * x) + q) * (x - H - q) := by rw [alg₁ x q hx]
        have : 0 < q := by aesop
        have h₇ : 0 < x - H - q := by
          have hp₁ : 0 < (x ^ 2 + 2) / (2 * x) + q := by positivity
          let A := (x ^ 2 + 2) / (2 * x) + q
          let B := (x - H - q)
          apply @rel₁ A B hp₁ h₆
        linarith

      have : x ≤ x - H := by
        simp [upperBounds] at H₃
        apply h₂
        intro v hv
        apply H₃
        exact hv
      norm_num at *
      have : ¬ 0 < H := by linarith
      contradiction
    push_neg at h₃
    exact h₃

  · --  2 ≤ x ^ 2 -- 1:07:07 (lecture 3)
    by_contra hc
    push_neg at hc
    have h₃ : 1 ≤ x := by apply h₁; unfold E; norm_num
    let H := min ((2-x^2)/(2*(2*x + 1))) (1/2)
    have H₁ : 0 < H := by
      dsimp [H]
      simp
      simp_all only [sub_pos, div_pos_iff_of_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      linarith
    have H₂ : H < 1 := by
      simp_all only [one_div, lt_min_iff, sub_pos, div_pos_iff_of_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left,
        inv_pos, and_true, min_lt_iff, H]
      right
      norm_num
    -- now prove that x + H ∈ E
    let φ := 2 * x + 1
    have h' : φ ≠ 0 := by aesop
    have H₃ : H ≤ ((2 - x^2)/(2*φ)) := by aesop

    have hxe := -- show (x + H) ^ 2 < 2
      calc (x + H)^2
        _= x^2 + 2*x*H + H^2 := by ring
        _< x^2 + 2*x*H + H := by nlinarith
        _= x^2 + φ*H := by ring
        _≤ x^2 + φ * ((2 - x^2) / (2*(2*x + 1))) := by rel [H₃]
        _= x^2 + φ * (1/(2*φ)) * (2 - x^2) := by ring
        _= x^2 + (φ / (2*φ)) * (2 - x^2) := by ring
        _= x^2 + (φ / (φ*2)) * (2 - x^2) := by ring
        _= x^2 + (1 / 2) * (2 - x^2) := by rw [div_mul_right 2 h']
        _< x^2 + (1    ) * (2 - x^2) := by
          have h₇ : 0 < 2 - x ^ 2 := by nlinarith
          gcongr; norm_num
        _= 2 := by ring

    have hxe₂ : (x + H)^2 < 2 → x + H ∈ E := by
      intro hh₁
      unfold E
      constructor
      · positivity
      · exact hh₁

    have hxe₄ : x + H ∈ E := by apply hxe₂; exact hxe

    have hxe₆ : ¬ IsLUB E x := by
      have con₂ := @h₁ (x + H) hxe₄
      have : ¬ 0 < H := by linarith
      contradiction
    contradiction


-- Theorem 12
-- ∃! r ∈ R such that r > 0 and r^2 = 2. In other words, √2 ∈ R but √2 ∉ Q.



-- step 1. E is bounded above (by 2 for instance),
-- step 2. establish that r := sup E, r ∈ ℝ
-- step 3. Show that 0 < r
-- step 4. Show that r^2 = 2.

-- We now prove uniqueness.
-- step 5. Suppose that there is a p > 0 with p^2 = 2.
--         Then, since (r + p) > 0,
-- 0 = r^2 − p^2
--   = (r + p)(r − p)
--   → r − p = 0
--   → r = p.

lemma step00 : 2 ∈ upperBounds E := by
  refine mem_upperBounds.mpr ?_
  intro x ⟨hx₁, hx₂⟩
  nlinarith

lemma step01 : 1 ∈ E := by simp [E]
lemma step02 : E.Nonempty := nonempty_of_mem step01

lemma step1 : BddAbove E := nonempty_of_mem step00

lemma step2 : ∃ r, IsLUB E r := by
  have h₀ :  1 ∈ E := by dsimp [E]; norm_num
  have h₁ : E.Nonempty := by exact nonempty_of_mem h₀
  exact Real.exists_isLUB h₁ step1

lemma step3 (r : ℝ) (h : IsLUB E r) : 0 < r := by
  dsimp [E, IsLUB, IsLeast] at *
  have ⟨h₁, _⟩ := h

  have : 1 ≤ r → 0 < r := by
    intro hr
    linarith
  apply this
  apply h₁
  norm_num


lemma step4 (r : ℝ) (h : IsLUB E r) : r^2 = 2 := by
  -- reuse your result from Lecture 3, but change ℚ to ℝ
  apply lubp_part_1
  exact h

theorem thm_12 : ∃! r : ℝ, 0 < r ∧ r ^ 2 = 2 := by
  have ⟨r, hr⟩ := step2
  use r
  simp
  constructor
  · refine ⟨step3 r hr, step4 r hr⟩
  · --
    intro y hy₁ hy₂
    have := step3 r hr
    have hh₁ : 0 ≤ y := by linarith
    have hh₂ : 0 ≤ r := by linarith
    rw [← sq_eq_sq hh₁ hh₂]
    rw [hy₂]
    exact (step4 r hr).symm

end theorem_12

end Lecture4
