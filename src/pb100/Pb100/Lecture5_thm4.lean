import Mathlib

import Pb100.Lecture5Util
import Pb100.Lecture5

namespace Lecture5

open Set

namespace thm_4

-- Lecture 5, Theorem 4, this is problem 4 from pset 3.

-- Let A ⊆ ℝ which is bounded above, and let x be an upper bound
-- for A. Prove that x = sup A ↔ ∀ ε > 0, ∃ a ∈ A such that x − ε < a.

-- either x ∈ A or a ∉ A.
-- obtain h | h := Classical.em (x ∈ A)



theorem theorem_4 (x : ℝ) (A : Set ℝ)
  (ha : BddAbove A) (he : A.Nonempty) (hx : x ∈ upperBounds A) :
    IsLUB A x ↔ ∀ ε > 0, ∃ a ∈ A, x - ε < a := by
  --
  -- this is a problem on the pset, but this theorem is used in lecture
  -- so, we need the statement. maybe import it from the pset?
  sorry


end thm_4



end Lecture5
