import Mathlib
import Pb100.Lecture5

namespace Lecture6
open Lecture5.abs_koan

namespace thm_1

theorem triangle_inequality (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rw [abs_le_iff_le_and_le (x + y) (|x| + |y|)]

  constructor
  · -- -(|x| + |y|) ≤ x + y
    calc -(|x| + |y|)
      _= -|x| + -|y| := by ring
      _≤ x + y := by rel [neg_abs_le x, neg_abs_le y]

  · -- x + y ≤ |x| + |y|
    rel [le_abs x, le_abs y]

end thm_1

namespace thm_2
open Set

variable (x : ℝ)

def interval := {x : ℝ | 0 < x ∧ x ≤ 1}

lemma set_bijection_on : ∃ f, Set.BijOn f (univ : Set ℕ) interval := by
  by_contra hc
  push_neg at hc

  sorry

theorem interval_is_uncountable : #(univ : Set ℕ) = #interval := by
  obtain ⟨f, hf⟩ := set_bijection_on
  mk_congr (BijOn.equiv f hf)


end thm_2
end Lecture6
