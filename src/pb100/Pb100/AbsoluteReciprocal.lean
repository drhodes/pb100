import Mathlib

namespace abs_recip

-- absolute reciprocals are analagous to absolute value

-- for absolute value, |a - b| = |b - a|
-- for absolute recip, abr(a / b) = abr(b / a)

@[reducible]
noncomputable
def abr (q: ℝ) :=
  if habr : |q| < 1
  then 1 / q
  else q

variable (p q : ℝ)

example : abr (1 / 2) = abr (2 / 1) := by
  unfold abr
  norm_num
  rw [abs_of_pos]
  linarith
  norm_num



 example (h: p < 1) : ¬ (1 < p) := by exact not_lt_of_gt h
--  lemma  (q : ℝ) (hp : 0 < q) (hq : q ≠ 0) (h : q < 1) : 1 < 1 / q := by
--   exact one_lt_one_div hp h


lemma qonv (q : ℝ) (hp : 0 < q) : q ≤ q⁻¹ ↔ q * q ≤ q⁻¹ * q := by exact Iff.symm (mul_le_mul_iff_of_pos_right hp)
lemma qonv' (q : ℝ) (hp : 0 < q) : q⁻¹ ≤ q ↔ q⁻¹ * q ≤ q * q := by exact Iff.symm (mul_le_mul_iff_of_pos_right hp)
lemma qonv₁ (q : ℝ) (h : q ≠ 0) : q * q⁻¹ = 1 := by exact CommGroupWithZero.mul_inv_cancel q h
lemma qonv₂ (q : ℝ) (h : q ≠ 0) : q⁻¹ * q = 1 := by exact inv_mul_cancel₀ h

lemma abr_lem1 (q : ℝ) (hp : 0 < q) : 0 < 1 / q := by
  exact one_div_pos.mpr hp

lemma abr_eq_abr_div_pos (hp : 0 < q) : abr q = abr (1 / q) := by
  obtain h | h | h := lt_trichotomy q 1
  · -- q < 1
    have hcon : 1 < 1 / q := one_lt_one_div hp h
    rw [abr, abs_of_pos]
    split_ifs
    rw [abr, abs_of_pos]
    split_ifs
    · norm_num at *
      have : ¬ q⁻¹ < 1 := by linarith
      contradiction
    · rfl
    · exact abr_lem1 q hp
    · contradiction
    · exact hp
  · -- q = 1
    rw [h]
    simp
  · -- 1 < q
    rw [abr, abs_of_pos hp]
    simp
    split_ifs
    have : ¬ q < 1 := by linarith
    contradiction
    rfl
    rfl
    rename_i h₁ h₂
    push_neg at h₁ h₂
    have hh₁ : 0 < q⁻¹ := by exact inv_pos_of_pos hp
    rw [abs_of_pos hh₁] at h₂
    rw [one_le_inv₀ hp] at h₂
    have : q = 1 := by
      rw [le_antisymm_iff]
      refine ⟨h₂, h₁⟩
    rw [this]
    norm_num

lemma abr_eq_abr_neg (q : ℝ) : abr q = - abr (- q) := by
  unfold abr
  split_ifs
  · ring
  · norm_num at *
    have : ¬ 1 ≤ |q| := by nlinarith
    contradiction
  · norm_num at *
    have : ¬ 1 ≤ |q| := by nlinarith
    contradiction
  · ring

lemma abr_odd (q : ℝ) : abr (-q) = - abr q := by
  unfold abr
  split_ifs
  · ring
  · norm_num at *
    have : ¬ 1 ≤ |q| := by nlinarith
    contradiction
  · norm_num at *
    have : ¬ 1 ≤ |q| := by nlinarith
    contradiction
  · ring

lemma abr_eq_abr_div_neg (hn : q < 0): abr q = abr (1 / q) := by
  let r := -q
  have hr : 0 < r := by aesop
  have h₁ := abr_eq_abr_div_pos r hr
  have hinv: r = -q := by aesop
  rw [hinv] at h₁
  rw [abr_odd q] at h₁
  have hodd : abr q = - abr (1 / -q) := by nlinarith
  have h : 1 / -q = - (1 / q) := by ring
  conv at hodd => rhs; rhs; rhs; rw [h]
  rwa [←abr_eq_abr_neg (1/q)] at hodd

theorem abr_eq_abr_div (hq : q ≠ 0): abr q = abr (1 / q) := by
  obtain h₁ | h₁ | h₁ := lt_trichotomy q 0
  · exact abr_eq_abr_div_neg q h₁
  · contradiction
  · exact abr_eq_abr_div_pos q h₁


theorem mul_abr_eq_abr_mul (hq : q ≠ 0): ¬ (p * abr q = abr (p * q)) := by
  simp [abr]
  obtain h₁ | h₁ | h₁ := lt_trichotomy p 0
  sorry



end abs_recip
