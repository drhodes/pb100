import Mathlib

namespace Lecture4

section theorem_10

open Set

-- Theorem 10

-- Let F be an ordered field with the least upper bound property. If A ⊂ F is
-- nonempty and bounded below, then inf A exists in F .

-- Proof :
-- Suppose A ⊂ F is nonempty and bounded below, i.e. ∃a ∈ F such that ∀x ∈ A, a ≤ x.
-- 1. Let -A = {−x | x ∈ A}.
-- 2. Then, ∀x ∈ A, −x ≤ −a ⇒ −a is an upper bound for -A.
-- 3. Since F has the least upper bound property, ∃c ∈ F such that c = sup -A.
-- 4. Then, ∀x ∈ A, −x ≤ c ⇒ ∀x ∈ A, −c ≤ x.
-- 5. Hence, −c is a lower bound for A.
-- 6. We have also shown that if a is a lower bound for A, then −a is an upper bound for -A.
-- 7. Therefore, c ≤ −a since c = sup -A ⇒ a ≤ −c.
-- 8. Hence, −c is the greatest lower bound for A.

-- Let F be an ordered field with the least upper bound property.
variable {F : Type} [ConditionallyCompleteLinearOrderedField F]

-- A ⊂ F
variable (A : Set F)

-- 1. Let -A = {−x | x ∈ A}.
#check -A

-- 2. Then, ∀x ∈ A, −x ≤ −a ⇒ −a is an upper bound for -A.
lemma step2 (a : F) (ha : a ∈ lowerBounds A) : -a ∈ upperBounds (-A) := by
  intro v hv
  exact le_neg_of_le_neg (ha hv)

-- 3. Since F has the least upper bound property, ∃c ∈ F such that c = sup -A.
lemma step3 (h₁ : (-A).Nonempty) (H : BddAbove (-A)): ∃ c, IsLUB (-A) c  := by
  use sSup (-A)
  apply isLUB_csSup h₁ H

-- 4. Then, ∀x ∈ A, −x ≤ c ⇒ ∀x ∈ A, −c ≤ x.
lemma step4 (c : F) : ∀ x ∈ A, -x ≤ c → -c ≤ x := by
  intro x _ hx
  linarith

-- 5. Hence, −c is a lower bound for A.
lemma step5 (c : F) (hc : c ∈ upperBounds (-A)) : (-c) ∈ lowerBounds A := by
  rw [mem_def]
  intro v hv
  apply step4 A c
  exact hv
  apply hc
  rw [mem_neg, neg_neg]
  exact hv

-- 6. We have also shown that if a is a lower bound for A, then −a is an upper bound for -A.
lemma step6 : ∀ v, lowerBounds A v → upperBounds (-A) (-v) := by
  intro v hv
  simp [upperBounds]
  intro x hx
  exact le_neg_of_le_neg (hv hx)

-- Let F be an ordered field with the least upper bound property. If A ⊂ F is
-- nonempty and bounded below, then inf A exists in F .

theorem thm_10 (h₁ : A.Nonempty) (h₂ : BddBelow A) : ∃ j, IsGLB A j := by
  have ⟨a, ha⟩ := h₂

  -- 2. Then, ∀x ∈ A, −x ≤ −a ⇒ −a is an upper bound for -A.
  have hub := step2 A a ha

  -- 3. Since F has the least upper bound property, ∃c ∈ F such that c = sup -A.
  have hna : (-A).Nonempty := by exact Nonempty.neg h₁
  have hba : BddAbove (-A) := by exact BddBelow.neg h₂

  obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := step3 A hna hba

  -- 4. Then, ∀x ∈ A, −x ≤ c ⇒ −c ≤ x.
  -- 5. Hence, −c is a lower bound for A.
  have h₅ := step5 A c hc₁

  -- 6. We have that if a is a lower bound for A, then −a is an upper bound for -A.
  have h₆ := step6 A

  -- 7. Therefore, c ≤ −a since c = sup B =⇒ a ≤ −c.
  have h₇ : c ≤ -a := hc₂ hub

  -- 8. Hence, −c is the greatest lower bound for A.
  use -c
  constructor
  · exact h₅
  · intro x hx
    apply le_neg_of_le_neg
    exact hc₂ (h₆ x hx)

end theorem_10

end Lecture4
