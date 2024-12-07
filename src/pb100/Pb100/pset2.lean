import Mathlib

namespace Pset2

open Finset

-- based on pset found at the following link:
-- https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/resources/mit18_100af20_hw2/

-- Exercises given with a numbering are from Basic Analysis: Introduction to
-- Real Analysis (Vol I) by J. Lebl.

-- --------------------------------------------------------------------------
section ex_1_1_1

-- Prove part (iii) of Proposition 1.1.8. That is, let 𝐹 be an ordered field
-- and 𝑥, 𝑦, 𝑧 ∈ 𝐹. Prove If 𝑥 < 0 and 𝑦 < 𝑧, then 𝑥𝑦 > 𝑥𝑧

variable {F : Type*} [LinearOrderedField F]
variable {x y z : F}

example (hx : x < 0) (hy : y < z) : x * z < x * y := by
  rw [mul_lt_mul_left_of_neg hx]
  exact hy

end ex_1_1_1


-- --------------------------------------------------------------------------
section ex_1_1_2

-- TODO verify that: Mathlib's LinearOrder ≡ Book's StrictTotalOrder.

-- Let 𝑆 be an ordered set. Let 𝐴 ⊂ 𝑆 be a nonempty finite subset. Then 𝐴 is
-- bounded. Furthermore, inf 𝐴 exists and is in 𝐴 and sup 𝐴 exists and is in
-- 𝐴. Hint: Use induction.

-- note: Induction not needed if using an available lemma.
-- see proof for: `Finset.exists_minimal`

variable {α : Type} [LinearOrder α]
variable (A : Finset α)

-- finite sets are bounded

lemma this_above [Nonempty α] : BddAbove (↑A : Set α) := by
  exact Finset.bddAbove A

lemma this_below [Nonempty α] : BddBelow (↑A : Set α) := by
  exact Finset.bddBelow A

lemma this_sup (h : A.Nonempty) : ∃ x, IsLUB (↑A : Set α) x := by
  have ⟨m, ⟨hm₁, hm₂⟩⟩ := A.exists_maximal h
  use m
  constructor
  · intro x hx
    push_neg at hm₂
    apply hm₂
    exact hx

  · intro y hy
    apply @hy m hm₁

-- same logic.
lemma this_inf (h : A.Nonempty) : ∃ x, IsGLB (↑A : Set α) x := by
  have ⟨m, ⟨hm₁, hm₂⟩⟩ := A.exists_minimal h
  use m
  constructor
  · intro x hx
    push_neg at hm₂
    apply hm₂
    exact hx

  · intro y hy
    apply @hy m hm₁

end ex_1_1_2



-- --------------------------------------------------------------------------
section ex_1_1_5

-- Exercise 1.1.5: Let 𝑆 be an ordered set. Let 𝐴 ⊂ 𝑆 and suppose 𝑏 is an
-- upper bound for 𝐴. Suppose 𝑏 ∈ 𝐴. Show that 𝑏 = sup 𝐴.

variable {α : Type} [LinearOrder α]
variable (A : Set α)
variable (b : α)

example (h₁ : b ∈ upperBounds A) (h₂ : b ∈ A) : IsLUB A b := by
  refine isLUB_iff_le_iff.mpr ?_
  intro c
  constructor
  · intro h a ha
    calc a
      _≤ b := h₁ ha
      _≤ c := h
  · intro h
    apply @h b h₂

end ex_1_1_5



-- --------------------------------------------------------------------------
section ex_1_1_6

-- Exercise 1.1.6: Let 𝑆 be an ordered set. Let 𝐴 ⊂ 𝑆 be nonempty and bounded
-- above. Suppose sup 𝐴 exists and sup 𝐴 ∉ 𝐴. Show that 𝐴 contains a
-- countably infinite subset

variable {α : Type} [LinearOrder α]
variable (m : α) (A : Set α)

-- Can the set A contain only 1 element? No, because that element would be sup.
-- Could A have uncountably infinite number of elements? No, for the same
-- reason.

-- Gut feeling? Somewhere in the definition of one of the upperbound
-- inequalities, the ≤ breaks down, it is either < or =, however it can't be =
-- because that would mean m is in A, so < remains, which will prove that m ∉ A.

example (h₁ : A.Nonempty) (h₂ : BddAbove A) (h₃ : IsLUB A m) (h₄ : m ∉ A) :
  Nat.card A = 0 := by
  --
  rw [Nat.card_eq_zero]
  simp [IsLUB, IsLeast, upperBounds, lowerBounds] at h₃
  obtain ⟨hl₁, hl₂⟩ := h₃
  have hm₁ := @hl₁ m
  left
  sorry



end ex_1_1_6



-- --------------------------------------------------------------------------
section ex_1_2_7

-- Prove the arithmetic-geometric mean inequality.
-- For two positive real numbers 𝑥, 𝑦, √(x * y) ≤ (x + y) / 2
-- And furthermore, equality occurs if and only if 𝑥 = 𝑦.

variable {x y : ℝ}

lemma lem1 (a b : ℝ) : 2 * a < b ↔ a < b / 2 := by
  symm
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

lemma step_ne (h : x ≠ y) {hx : 0 < x} {hy : 0 < y} : √ (x * y) < (x + y) / 2 := by
  rw [← lem1]
  sorry

lemma step_eq (h : x = y) {hx : 0 < x} {hy : 0 < y} : √ (x * y) = (x + y) / 2 := by
  rw [h]
  norm_num
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]
  exact hy


example (hx : 0 < x) (hy : 0 < y) : √ (x * y) ≤ (x + y) / 2 := by
  rw [le_iff_lt_or_eq]
  cases eq_or_ne x y with
  | inr h => left; exact @step_ne x y h hx hy
  | inl h => right ; exact @step_eq x y h hx hy


end ex_1_2_7


-- --------------------------------------------------------------------------
section ex_1_2_9

-- Let 𝐴 and 𝐵 be two nonempty bounded sets of real numbers.
-- Let 𝐶 := {𝑎 + 𝑏 : 𝑎 ∈ 𝐴, 𝑏 ∈ 𝐵}.
-- Show that 𝐶 is a bounded set and that
-- sup 𝐶 = sup 𝐴 + sup 𝐵 and inf 𝐶 = inf 𝐴 + inf 𝐵.

variable {A B : Set ℝ}
--variable [hna : Nonempty A] [hnb : Nonempty B]

def C (A B : Set ℝ) : Set ℝ := { p.1 + p.2 | p ∈ Set.prod A B }

-- this is the book's definition
def bdd (X : Set ℝ) := BddBelow X ∧ BddAbove X

lemma c_bdd_below (h₁ : BddBelow A) (h₂ : BddBelow B) : BddBelow (C A B) := by
  simp [C]
  obtain ⟨v, hv⟩ := h₁
  obtain ⟨w, hw⟩ := h₂
  use v + w
  intro z hz
  obtain ⟨j, ⟨k, ⟨hjk, hk⟩⟩⟩ := hz
  rw [←hk]
  unfold lowerBounds at hv hw
  rw [Set.prod] at hjk
  obtain ⟨hj₁, hk₁⟩ := hjk
  have hv₁ := @hv j hj₁
  have hw₁ := @hw k hk₁
  rel [hv₁, hw₁]

lemma c_bdd_above (h₁ : BddAbove A) (h₂ : BddAbove B) : BddAbove (C A B) := by
  simp [C]
  obtain ⟨v, hv⟩ := h₁
  obtain ⟨w, hw⟩ := h₂
  use v + w
  intro z hz
  obtain ⟨j, ⟨k, ⟨hjk, hk⟩⟩⟩ := hz
  rw [←hk]
  unfold upperBounds at hv hw
  rw [Set.prod] at hjk
  obtain ⟨hj₁, hk₁⟩ := hjk
  have hv₁ := @hv j hj₁
  have hw₁ := @hw k hk₁
  rel [hv₁, hw₁]

-- part 1. Show that 𝐶 is a bounded set
lemma c_bdd (h₁ : bdd A) (h₂ : bdd B) : bdd (C A B) := by
  constructor
  · exact c_bdd_below h₁.left h₂.left
  · exact c_bdd_above h₁.right h₂.right

lemma l₁ (x y z : ℝ) : x ≤ z - y → x + y ≤ z:= by
  intro h
  linarith

lemma l₂ (x y z : ℝ) : x + y ≤ z  →  x ≤ z - y := by
  intro h
  linarith

-- part 2. Show that sup 𝐶 = sup 𝐴 + sup 𝐵
example (x y z : ℝ) (h₁ : IsLUB A x) (h₂ : IsLUB B y) (h₃ : IsLUB (C A B) z) : z = x + y := by
  obtain ⟨hx₁, hx₂⟩ := h₁
  obtain ⟨hy₁, hy₂⟩ := h₂
  obtain ⟨hz₁, hz₂⟩ := h₃

  rw [le_antisymm_iff]

  constructor
  · -- z ≤ x + y
    dsimp [C, upperBounds, lowerBounds, Set.prod] at *
    have hh₃ := @hz₂ (x + y)
    apply hh₃
    intro t ht
    obtain ⟨p, hp⟩ := ht
    obtain ⟨hp₁, hp₂⟩ := hp
    obtain ⟨hpp₁, hpp₂⟩ := hp₁
    have hh₁ := @hx₁ p.1 hpp₁
    have hh₂ := @hy₁ p.2 hpp₂
    rw [←hp₂]
    rel [hh₁, hh₂]

  · -- x + y ≤ z
    dsimp [C, upperBounds, lowerBounds, Set.prod] at *
    have hh₁ := @hx₂ (z - y) -- ok this is on the right track
    apply l₁
    apply hh₁
    intro v hv

    have hh₂ := @hy₂ (-v + z)
    have : y ≤ -v + z → v ≤ z - y := by intro h; linarith
    apply this
    apply hh₂
    intro w hw

    have : v + w ≤ z → w ≤ -v + z := by intro h; linarith
    apply this
    apply @hz₁ (v + w)

    use (v, w)

-- part 3. Show that inf 𝐶 = inf 𝐴 + inf 𝐵


end ex_1_2_9



end Pset2
