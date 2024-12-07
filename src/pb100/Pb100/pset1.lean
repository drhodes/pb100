import Mathlib

open Set Function

-- exercise 0.3.6 part a

example {A B C : Set α} : (A ∩ (B ∪ C)) = (A ∩ B) ∪ (A ∩ C) := by
  dsimp [union_def]
  ext x
  aesop

  -- constructor
  -- · intro h
  --   repeat dsimp
  --   repeat rw [inter_def] at *
  --   dsimp at h
  --   obtain ⟨ha, hbc⟩ := h
  --   dsimp at *
  --   cases hbc with
  --   | inl h => left; aesop
  --   | inr h => right; aesop
  -- · aesop


-- exercise 0.3.6
example {A B C : Set α} : (A ∪ (B ∩ C)) = (A ∪ B) ∩ (A ∪ C) := by
  aesop


-- exercise 0.3.9
example : powerset ({}:Set ℕ) = {∅} := by
  dsimp [powerset, subset_def]
  ext a
  constructor
  · dsimp
    intro h
    ext x
    constructor
    · apply h
    · aesop  --TODO
  · intro h
    dsimp at *
    aesop -- TODO


-- 2) Exercise 0.3.11: Prove by induction that 𝑛 < 2𝑛 for all 𝑛 ∈ ℕ.
example {n: ℕ} (h: 1<n): n < 2*n := by
  -- We need to compensate for the fact that the book has natural numbers that
  -- start at 1.  To do that, instead of passing the induction' tactic the
  -- variable n, rather pass it the hypothesis `h`.
  induction' h with k hk ih
  · norm_num
  · rw [Nat.succ_eq_add_one]
    calc k + 1
      _< k + 1 + k + 1 := by linarith
      _= 2 * (k+1) := by ring


-- Exercise 0.3.15: Prove that 𝑛^3 + 5𝑛 is divisible by 6 for all 𝑛 ∈ ℕ.
example (n:ℕ) (h: 0 < n) : 6 ∣ n^3 + 5*n := by
  dsimp [(· ∣ ·)]
  induction' h with k hk ih
  · -- case: n = 1
    rw [Nat.succ_eq_add_one]
    use 1;
    ring
  · -- case: 1 < n
    rw [Nat.succ_eq_add_one] at *
    obtain ⟨p, hp⟩ := ih
    have h₀ :=
      calc (k+1)^3 + 5*(k + 1)
        _= k^3 + 5*k + 3*k^2 + 3*k + 6 := by ring
        _= 6*p + 3*k^2 + 3*k + 6 := by rw [hp]
    rw [h₀]

    cases Nat.even_or_odd k with
    | inl h₁ =>
      · --
        obtain ⟨q, hq⟩ := h₁
        rw [hq]
        have h₂ :=
          calc 6 * p + 3 * (q + q)^2 + 3 * (q + q) + 6
            _= 6 * (p + 2 * q^2 + q + 1) := by ring
        rw [h₂]
        use (p + 2 * q ^ 2 + q + 1 )

    | inr h₁ =>
      · --
        obtain ⟨q, hq⟩ := h₁
        rw [hq]
        have h₂ :=
          calc 6 * p + 3 * (2*q + 1) ^ 2 + 3 * (2*q + 1) + 6
            _= 6 * (p + 2 * q^2 + 2*q + q + 2) := by ring
        rw [h₂]
        use (p + 2 * q^2 + 2*q + q + 2)


-- 3. Exercise 0.3.12: Show that for a finite set 𝐴 of
--    cardinality 𝑛, the cardinality of 𝒫(𝐴) is 2^n


def inj {A: Set α) (B: Set β) (f: α→β) := ∀x ∈ A, ∀y ∈ A, (f x ∈ B) ∧ (f y ∈ B) ∧ f x = f y → x = y
def sur (A: Set α) (B: Set β) (f: α→β) := ∀y ∈ B, ∃x ∈ A, f x ∈ B ∧ f x = y
def bij (A: Set α) (B: Set β) (f: α→β) := inj A B f ∧ sur A B f

def card_eq (A: Set α) (B: Set β) := ∃ f, bij A B f
def card_le (A: Set α) (B: Set β) := ∃ f, inj A B f
def card_lt (A: Set α) (B: Set β) := ∃ f, inj A B f ∧ ¬ bij A B f

def P₁ (n:ℕ): Set (Set ℕ) := powerset {x | x < n}
def C₁ (n:ℕ): Set (BitVec n) := {BitVec.ofNat n x | x < 2^n}

def setOfBitVec (bv : BitVec n) :=  ⋃₀ { if bv[i]! = true then {i} else {} | i < n}

example (n:ℕ) : card_eq (C₁ n) (P₁ n) := by
  dsimp [card_eq, bij]
  use setOfBitVec
  constructor
  · --
    dsimp [inj]
    intro x hx y hy ⟨h₁, h₂, h₃⟩
    dsimp [setOfBitVec] at h₃
    sorry
  · --
    dsimp [sur]
    intro y hy
    sorry





-- Exercise 0.3.19: Give an example of a countably infinite collection of finite
-- sets 𝐴1 , 𝐴2 , . . ., whose union is not a finite set.

-- def example0319 : ⋃₀ {{x:ℕ} | x ∈ ℕ}



--theorem product_of_primes (q : ℚ) (hq: 0 < q) (hd: q.den = 1) (h₁: q ≠ 1) (N: ℕ) := by
--  sorry --  q = ∏ 1 N -- TODO

-- def S (n:ℕ) := Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1))

-- example (f : ℝ × ℝ → ℝ) : Filter.Tendsto (fun (n : ℕ) ↦ ((S n) ×ˢ (S n)).indicator f x)
--     Filter.atTop (nhds ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator f x)) := by
--     repeat aesop <;> repeat
--   sorry
