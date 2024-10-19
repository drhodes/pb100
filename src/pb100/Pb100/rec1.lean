import Mathlib.Tactic
import Mathlib.Tactic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Data.Multiset.Basic

open Vector Multiset

theorem sum_distrib (xs: Finset ℝ) : (∑ x ∈ xs, 2*x) = (2 * ∑ x ∈ xs, x) := by
  sorry


section AMGM

-- base case of induction in AMGM
lemma amgm_base_case
  (xs: Finset ℝ)
  (h : 1 = xs.card) :
  (map (fun x ↦ x) xs.val).prod ≤ (map (fun x ↦ x) xs.val).sum := by

  -- prove that mapping id over a set is just the set.
  have h₁ : (map (fun x ↦ x) xs.val) = xs.val := by
    exact map_id' xs.val
  --
  rw [h₁]
  rw [prod]
  sorry

lemma step_ih
  (n : ℕ)
  (xs : Finset ℝ)
  (k : ℕ)
  (ih : k = xs.card → (∏ x ∈ xs, x) ^ (1 / k) ≤ ∑ x ∈ xs, x / ↑k)
  (h : k + 1 = xs.card)
  (hk : 1 ≤ k) : (∏ x ∈ xs, x) ^ (1 / (k + 1)) ≤ ∑ x ∈ xs, x / (↑k + 1) := by
    sorry


theorem AMGM (xs: Finset ℝ) (h: n = xs.card) (hn: 0 < n) : (∏ x ∈ xs, x)^(1/n) ≤ (∑ x ∈ xs, x/n) := by
  induction' hn with k hk ih
  · -- base case n = 1,
    rw [Nat.succ_eq_add_one] at *
    norm_num at *
    rw [Finset.prod, Finset.sum]
    apply (amgm_base_case xs h)

  · -- inductive step
    rw [Nat.succ_eq_add_one] at *
    norm_num at *
    apply (step_ih n xs k ih h hk)


end AMGM




-- theorem arith_geo_mean_ineq
