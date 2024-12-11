import Mathlib


lemma lt_cube_of_lt₁ (r : ℝ) (hr : 0 < r ^ 3) : 0 < r := by
  obtain h | h | h := (lt_trichotomy r 1)
  · --
    have rsqpos : 0 ≤ r * r := by exact mul_self_nonneg r

    have rnot0 : 0 ≠ r := by
      by_contra hc
      rw [←hc] at hr
      norm_num at hr

    have r_sq_lt_r :=
      calc 0
        _< r ^ 3 := hr
        _= r * r * r := by ring
        _< r * r * 1 := by rel [h]
        _= r ^ 2 := by ring

    have hr3 : r * r ^ 2 = r ^ 3 := by exact Eq.symm (pow_succ' r 2)
    rw [←hr3] at hr
    have hms : r * r = r^2 := by exact Eq.symm (pow_two r)
    rw [hms] at rsqpos

    have := pos_of_mul_pos_left hr rsqpos
    exact this

  · linarith
  · linarith



lemma lt_cube_of_one_lt (r : ℝ) (hr : 1 < r ^ 3) : 1 < r := by
  have : Odd 3 := by exact Nat.odd_iff.mpr rfl

  have rsqpos : 0 ≤ r * r := by exact mul_self_nonneg r

  have lt_cube := lt_cube_of_lt₁ r ?_

  nlinarith
  nlinarith
