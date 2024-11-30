-- Lecture3.lean, part 1
import Mathlib
-- import Mathlib.Algebra.ModEq
-- import Mathlib.Data.Set.Basic
-- import Mathlib.Logic.Basic
-- import Mathlib.Order.Bounds.Basic
-- import Mathlib.Order.Notation


namespace Lecture3

def inj (A: Set α) (B: Set β) (f: α→β) := ∀x ∈ A, ∀y ∈ A, (f x ∈ B) ∧ (f y ∈ B) ∧ f x = f y → x = y
def sur (A: Set α) (B: Set β) (f: α→β) := ∀y ∈ B, ∃x ∈ A, f x ∈ B ∧ f x = y
def bij (A: Set α) (B: Set β) (f: α→β) := inj A B f ∧ sur A B f

def card_eq (A: Set α) (B: Set β) := ∃ f, bij A B f
def card_le (A: Set α) (B: Set β) := ∃ f, inj A B f
def card_lt (A: Set α) (B: Set β) := ∃ f, inj A B f ∧ ¬ card_eq A B

open Set

section cantor₁

theorem cantor (A: Set α) : card_lt A (powerset A) := by
  use (λ x => {x}) -- choose some f where f(x) = {x}
  constructor
  · -- inj A (𝒫 A) fun x ↦ {x}
    intro x hx y hy h
    obtain ⟨_, _, h₁⟩ := h
    dsimp at *
    rw [←singleton_eq_singleton_iff]
    exact h₁
  · -- |A| ≠ |𝒫 A|
    by_contra h
    dsimp [card_eq] at h
    obtain ⟨g, hg⟩ := h

    let B := {x ∈ A | x ∉ g x}
    have hb : B ∈ 𝒫 A := @mem_of_mem_diff α A (λ x => g x x)

    obtain ⟨h₁, h₂⟩ := hg
    rw [sur] at h₂

    have hg : ∃ b ∈ A, g b = B := by
      obtain ⟨x, ⟨hx₁, _, hx₂⟩⟩ := h₂ B hb
      use x

    obtain ⟨b, ⟨hb₁, hb₂⟩⟩ := hg

    cases (Classical.em (b ∈ g b)) with
    | inl h =>
      · have hc := h
        dsimp [B] at hb₂
        rw [hb₂] at h
        obtain ⟨_, hc₂⟩ := h
        contradiction
    | inr h =>
      · have hc := h
        dsimp [B] at hb₂
        rw [hb₂] at h
        simp at h
        have := h hb₁
        contradiction

end cantor₁

/-!

Goal : To describe ℝ

Theorem: There exists a unique ordered field containing ℚ with the least upper
bound property that is denoted by ℝ


-/

-- defining ordered sets and fields.

namespace ex₂

-- can an ordering be created
-- (P ∧ ¬Q ∧ ¬R) ∨ (¬P ∧ Q ∧ ¬R) ∨ (¬P ∧ ¬Q ∧ R)


local infix:50 "≺"  => λ (A B : Set ℕ) => (A ⊆ B)

lemma ord_refl : Reflexive (· ≺ ·) := by
  dsimp [Reflexive]
  intro x
  norm_num

lemma ord_not_symm : ¬ Symmetric (· ≺ ·) := by
  dsimp [Symmetric]
  push_neg
  use {1}, {1,2}
  constructor
  · norm_num
  · norm_num

lemma ord_antisymm : AntiSymmetric (· ≺ ·) := by
  dsimp [AntiSymmetric]
  intro x y h₁ h₂
  dsimp [Set.subset_def] at *
  ext w
  constructor
  · apply h₁ w
  · apply h₂ w

lemma ord_trans : Transitive (· ≺ ·) := by
  dsimp [Transitive]
  intro x y z hx hy
  trans y
  apply hx
  apply hy


--def PartialOrder := Reflexive (· ≺ ·) ∧ AntiSymmetric (· ≺ ·) ∧ Transitive (· ≺ ·)

def PartialOrder (α: Set ℕ → Set ℕ → Prop) := Reflexive α ∧ AntiSymmetric α ∧ Transitive α

-- Ok, it's a partial order
example : PartialOrder (· ≺ ·) := by
  unfold PartialOrder
  refine ⟨ord_refl, ord_antisymm, ord_trans⟩


def StrictOrder' (α: Set ℕ → Set ℕ → Prop) := Irreflexive α ∧ AntiSymmetric α ∧ Transitive α

-- #check StrictOrdered.eq_of_rel

-- (h_symm : @Symmetric α r) (h_trans : @Transitive α r)



example : ¬ StrictOrder' (· ≺ ·) := by
  unfold StrictOrder'
  push_neg
  intro h₁ _ _
  have : ¬ Irreflexive (· ≺ ·) := by
    unfold Irreflexive
    push_neg
    use {1}
  contradiction

end ex₂

-- example ℤ is StrictOrdered with relation m > n ↔ m - n ∈ ℕ
-- example ℚ is StrictOrdered with relation p > q ↔ ∃m,n ∈ ℕ, p - q = m/n - n ∈ ℕ
-- example ℚ×ℚ is StrictOrdered with relation (q,r) > (s,t) ↔ q>s ∨ q=s ∧ r>t


-- Definition 11 (Bounded Above/Below)

-- Let S be an ordered set and let E ⊂ S. Then,

-- 1. If there exists a b ∈ S such that x ≤ b for all x ∈ E, then E is bounded
--    above and b is an least upper bound of E.

-- 2. If ∃c ∈ S such that x ≥ c for all x ∈ E, then E is bounded below and c is
--    a lower bound of E.


def StrictOrder {r: Type} (α: r → r → Prop) :=
  Irreflexive α ∧ AntiSymmetric α ∧ Transitive α



namespace bounded
-- variable (f: α → α → Prop)
-- local infix:50 "≺"  => λ (A B) => f A B

-- Definition 11 (Bounded Above / Below)

namespace example12_term


def E : Set ℤ := {-2, -1, 0, 1, 2}

-- thanks to Jireh Loreaux for providing this proof
example: BddAbove E := ⟨2, by aesop (add simp [E])⟩

end example12_term

namespace example12

def E : Set ℤ := {-2, -1, 0, 1, 2}

example: BddAbove E := by
  use 3
  intro x h
  aesop (add simp [E]) -- todo explain how this is working.

example : IsLUB E 2 := by
  constructor
  · unfold upperBounds
    dsimp
    intro a
    aesop (add simp [E])
  · --
    dsimp [upperBounds, lowerBounds]
    intro a h
    have h₁ := @h 2
    apply h₁
    dsimp [E]
    simp

def S₁ := {n:ℕ | n < 3}

example : IsLUB S₁ 2 := by
  constructor
  · --
    dsimp [upperBounds, S₁]
    intro a h
    linarith
  · --
    dsimp [lowerBounds, upperBounds, S₁]
    intro a h
    apply (@h 2)
    norm_num

-- OK!
lemma rat_refl : ∀x:ℚ, x ≤ x := by simp

lemma rat_antisymm'  (x y : ℚ) : ( x ≤ y ) ∧ ( y ≤ x ) → x = y := by
  contrapose
  push_neg
  intro h₁ h₂
  rw [le_iff_lt_or_eq] at h₂
  cases h₂ with
  | inl h => exact h
  | inr h => contradiction

lemma rat_trans  (x y z: ℚ) : ( x ≤ y ) ∧ ( y ≤ z ) → x ≤ z := by
  intro h
  obtain ⟨h₁, h₂⟩ := h
  trans y
  exact h₁
  exact h₂

def ub (s: Set α) [LE α] := { b : α | ∀ a ∈ s, a ≤ b }

-- An element l of S is the supremum or least upper bound (l.u.b.)
-- sup E for E if:
-- (a) l is an upper bound for E;
-- (b) If b is an upper bound for E, then l ≤ b
def Sup (s: Set α) (l: α) [LE α] := l ∈ (ub s) ∧ ∀ b ∈ s, b ∈ (ub s) → l ≤ b

-- Hi all, I'm having trouble showing the 3 is the least upper bound of the
-- following set S:

def S := {q : ℚ | q < 3 }

-- I should say that I'm using the mathlib definition to try to prove it like this:

example: IsLUB S 3 := by sorry

-- And I'm sorry'ing out, because I could not prove that. I started unpacking
-- the definition to try to narrow down where the problem is.

-- sanity check, is 3 in the upperBounds?
lemma three_in_ub : 3 ∈ upperBounds S := by
  dsimp [upperBounds, S]
  intro x h
  linarith -- ok.

-- is everything greater than or equal to 3 in the upperbounds?
lemma ge_three_in_ub (r : ℚ) (h: 3 ≤ r): r ∈ upperBounds S := by
  dsimp [upperBounds, S]
  intro x h
  linarith -- ok.

-- Here are the innards of: IsLUB S 3
example: IsLeast (upperBounds S) 3 := by
  constructor
  · -- 3 ∈ upperBounds S
    apply three_in_ub
  · -- 3 ∈ lowerBounds (upperBounds S)
    sorry
    -- trying to prove this below: three_in_lb_of_ub.

lemma three_in_lb_of_ub : 3 ∈ lowerBounds (upperBounds S) := by
  dsimp [lowerBounds]
  intro a h
  dsimp [upperBounds] at h
  have h₁ := @h 3
  have h₂ : 3 ∉ S := by dsimp [S]; linarith
  apply h₁
  sorry -- stuck.

-- I could really use a hand proving the lemma `three_in_lb_of_ub`, or in case
-- I'm simply just wrong, I would appreciate that. If I should not be using
-- IsLUB for this, then that would also be helpful to know.

--example : T = upperBounds S := by

/- Luigi's "brute force solution" -/
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.E2.9C.94.20Least.20Upper.20Bound.2C.20IsLUB.20and.20the.20stubborn.20set.2E

example: IsLUB S 3 := by
  refine isLUB_iff_le_iff.mpr ?_
  intro b
  constructor
  · intro hb
    simp [upperBounds, S]; intros; linarith
  · contrapose!
    intro hb
    simp [upperBounds, S]
    refine ⟨b + (3-b)/2, by linarith, by simp [hb]⟩

example: IsLUB S 3 := by
  rw [isLUB_iff_le_iff]
  intro b
  constructor
  · intro hb
    simp [upperBounds, S];
    intro a h₁
    linarith
  · contrapose!
    intro hb
    dsimp [upperBounds, S]
    push_neg
    use b + (3-b)/2
    constructor
    · linarith
    · linarith


end example12

--
end bounded



namespace example12₃

def S := {q:ℚ | 0 ≤ q ∧ q < 1}

example : IsGLB S 0 := by
  constructor
  · simp [lowerBounds, S]
    intros; linarith
  · intro x h
    simp [lowerBounds, S] at h
    apply (@h 0)
    repeat norm_num

example : IsLUB S 1 := by
  rw [isLUB_iff_le_iff]
  intro x
  constructor
  · intro h
    simp [upperBounds, S]
    intros
    linarith
  · --
    contrapose!
    intro h₁
    dsimp [upperBounds, S]
    push_neg
    cases lt_or_le x (-1)
    · -- case: x < -1
      use 1/2
      refine ⟨by norm_num, by linarith⟩
    · -- case: -1 ≤ x
      use (x+1)/2
      refine ⟨⟨by linarith, by linarith⟩, by linarith⟩

end example12₃


-- Keep this theorem + proof.
namespace theorem_14

def E := {q : ℚ | 0 < q ∧ q^2 < 2}

-- the notes have: 0 ≤ x, but should be 1 ≤ x ?
-- https://youtu.be/nbENJ-Ce7Nc?t=3947

-- note about the lecture, Dr. Rodrigeuz later uses 1 < x instead of 1 ≤ x.??

lemma part₁ (x : ℚ) : IsLUB E x → 1 ≤ x:= by
  -- since 1 ∈ E
  have h₁ : 1 ∈ E := by dsimp [E]; aesop
  intro h₂
  obtain ⟨h₃, _⟩ := h₂
  dsimp [upperBounds] at h₃
  apply h₃
  exact h₁


-- https://youtu.be/nbENJ-Ce7Nc?t=4053
lemma part₂ (x : ℚ) : IsLUB E x → 2 ≤ x^2 := by
  by_contra hc
  push_neg at hc

  -- define h to break an inequality.
  set h := min (1 / 2) (2 - x^2) / (2 * (2*x + 1))
  have h₁ : h < 1 := by sorry
  have h₀ : 0 < h := by sorry
  have hx : 0 < x := by
    have hp := part₁ x hc.left
    linarith

  -- since x^2 < 2
  obtain ⟨h₂, h₃⟩ := hc

  have h₄ : x + h ∈ E := by
    -- x plus a positive number is bigger than x.
    have :=
    calc (x + h)^2
      _= x^2 + 2*x*h + h^2 := by ring
      _< x^2 + 2*x*h + h := by nlinarith
      _= x^2 + (2*x + 1) * 1 * h := by ring
      _< x^2 + (2*x + 1) * 2 * h := by
        have hr₁ : 1 < (2:ℚ) := by norm_num
        rel [hr₁]

      _≤ x^2 + (2*x + 1) * (2 - x^2) / (2 * (2*x + 1)) := by sorry
      _= x^2 + ((2*x + 1) / (2*x + 1)) * ((2 - x^2) / 2) := by sorry
      _< x^2 + 2 - x^2 := by sorry
      _= 2 := by ring
    sorry

  -- x + h ∈ E, however that's impossible because sup E < x + h.
  have h₄ : x + h < x := by sorry -- show this.
  have : ¬ (0 < h) := by linarith
  contradiction


-- https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/mit18_100af20_lec32.pdf#page=4
-- Prove that x^2 ≤ 2
lemma part₃ (x : ℚ) : IsLUB E x → x^2 ≤ 2 := by
  intro h
  -- assert that 1 ≤ x
  have h₁ := part₁ x h

  set h := (x^2 - 2) / (2 * x)

  -- suppose 2 < x^2
  have : 2 < x^2 → 0 < h → 0 < x - h := by
    intro h2 h3
    have hs :=
      calc 2
        _< 2 + h^2 := by nlinarith
        _= x^2 - (x^2 - 2) + h^2 := by linarith
        _= x^2 - 2*x*h + h^2 := by sorry
        _= (x - h)^2 := by sorry
    sorry
  sorry

-- https://youtu.be/nbENJ-Ce7Nc?t=3839
-- if x = sup E then 1 ≤ x and x^2 = 2.
theorem thm_14 (x : ℚ) : IsLUB E x → 1 ≤ x ∧ x^2 = 2 := by
  intro h
  constructor
  · -- ⊢ 1 ≤ x
    -- since 1 is in E, and x = sup E, then 1 ≤ x.
    apply part₁ x h

  · -- ⊢ x ^ 2 = 2
    -- case split, prove equality by proving two inequalities.
    rw [le_antisymm_iff]

    constructor
    · -- ⊢ x^2 ≤ 2
      apply part₃ x h
    · -- ⊢ 2 ≤ x^2
      apply part₂ x h

-- https://youtu.be/mlPLLXHZ8_U?t=581

lemma two_is_ub : 2 ∈ upperBounds E := by
  intro a h
  obtain ⟨h₁, h₂⟩ := h
  nlinarith





-- prove that the rational numbers do not have the least upper bound property
-- using ordering, originally by Dedekind.

-- from : https://youtu.be/mlPLLXHZ8_U?t=890
-- to   : https://youtu.be/mlPLLXHZ8_U?t=1579

example : ¬ ∃ x : ℚ, IsLUB E x := by
  by_contra h
  obtain ⟨x, hx⟩ := h
  sorry



end theorem_14



namespace page24

def lowest_terms (q : ℚ) := Int.gcd q.num q.den = 1

def S := {x : ℚ | x^2 < 2}



example : ¬ ∃ q:ℚ, IsLUB S q := by
  -- TODO
  push_neg
  intro q
  simp [IsLUB, IsLeast]
  intro h₁
  simp [upperBounds, lowerBounds, S] at *
  use (q + 1) / 2
  constructor
  · --
    intro a h₂
    sorry
  · sorry




end page24



namespace q_no_lubp

def lubp (S : Set α) [Preorder α] :=
  ∀ E ⊆ S, ∃ b ∈ S, E ≠ ∅ ∧ BddAbove E ∧ IsLUB E b

#check univ ℚ

theorem not_lubp_rat : ¬ lubp {q | q : ℚ} := by
  sorry


def E := {q : ℚ | 0 < q ∧ q^2 < 2}

-- theorem cancel_lemma₁ (a b : ℚ) (h : a≠0) : (a/(a*b)) = (1/b) := by
--   exact div_mul_right b h


lemma alg₁ (x q : ℚ) (h : x ≠ 0):
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

lemma rel₁ (a b : ℚ) {ha : 0 < a} {hab : 0 < a * b} : 0 < b := by
  exact (pos_iff_pos_of_mul_pos hab).mp ha


lemma rat_part_1 (x : ℚ) : IsLUB E x → 1 ≤ x ∧ x^2 = 2 := by
  --
  intro h₉
  have con₁ := h₉
  dsimp [IsLUB, IsLeast, upperBounds, lowerBounds] at h₉
  obtain ⟨h₁, h₂⟩ := h₉
  constructor
  · -- 1 ≤ x
    apply h₁
    unfold E; norm_num
  · -- ⊢ x ^ 2 = 2
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
          have hx : 0 < x := by linarith
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


    · --  2 ≤ x ^ 2 -- 1:07:07
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

/-

Suppose there exists an x ∈ ℚ, x = sup E.
Then by our previous theorem, x^2 = 2.
Note that 1 < x as otherwise x ≤ 1 → 2 = x^2 < 1^2
Thus, ∃ m, n ∈ ℕ such that n < m and x = m/n.
Therefore ∃ n ∈ ℕ, n * x ∈ ℕ
Define S := {k ∈ ℕ | k*x ∈ ℕ}
Then S ≠ ∅, since n ∈ S.
By well ordering of ℕ, S has least element k₀.
Let k₁ = k₀*x - k₀ ∈ ℤ
Then k₁ = k₀ * (x - 1) < k₀ * (2 - 1) = k₀.
So, k₁ ∈ ℕ and k₁ < k₀ → k₁ ∉ S because k₀ is the least element of S.
But, x*k₁ = k₀*x^2 - x*k₀ = 2*k₀ - x*k₀ = k₀-k₁ ∈ ℕ → k₁ ∈ S
This is a contradiction. Thus, ∄x ∈ ℚ such that x = sup E.

-/


lemma rat_den_unity_is_int (q: ℚ) (h : q.den = 1) : ∃ n : ℤ, n = q := by
  exact CanLift.prf q h

lemma rat_eq_iff_num_dem (q r : ℚ) : q.num = r.num ∧ q.den = r.den → q = r := by
  intro h
  obtain ⟨h₁, h₂⟩ := h
  exact Rat.ext h₁ h₂

lemma rat_den_unity_is_nat (q: ℚ) (h₁ : q.den = 1) (h₂ : 0 ≤ q ): ∃ n : ℕ, n = q := by
  use q.num.toNat
  apply Rat.ext
  · aesop
  · aesop

lemma lem₄ (k₀ : ℕ) (x : ℚ) (h₁ : 1 < x) (h₂ : 0 < k₀) : k₀ < k₀ * x := by
  calc ↑k₀
    _= ↑k₀ * (1:ℚ) := by ring
    _< ↑k₀ * x := by rel [h₁]

lemma coerce_sub_dist (a b : ℕ) : ↑(a - b) = ↑a - ↑b := by rfl

theorem coerce_dist (a b : ℤ) (x : ℚ) : x * ↑(a - b) = x * (↑a - ↑b) := by
  aesop





theorem rationals_have_holes : ¬ ∃ x, IsLUB E x := by
  by_contra hc
  have hc₁ := hc
  obtain ⟨x, hx⟩ := hc
  obtain ⟨hr₁, hr₂⟩ := rat_part_1 x hx
  obtain ⟨hx₁, hx₂⟩ := hx
  --dsimp [upperBounds, lowerBounds] at *
  let m := x.num
  let n := x.den
  let S := {k : ℕ | (k * x).den = 1 ∧ 0 < k}

  have hn₁ : 0 < n := by exact Rat.den_pos x
  have n_is_el : n ∈ S := by aesop
  have ht : S.Nonempty := by exact nonempty_of_mem n_is_el

  have hle : ∃ k , IsLeast S k := by
    use (sInf S)
    constructor
    · apply Nat.sInf_mem ht
    · exact (isLeast_csInf ht).right

  obtain ⟨k₀, hk⟩ := hle
  have hkq₁ : k₀ ∈ S := by exact mem_of_mem_inter_left hk

  let k₀x' := k₀ * x
  have h₁k₀x : (k₀x').den = 1 := by aesop
  have h₂k₀x : 0 ≤ k₀x' := by positivity
  obtain ⟨k₀x, hk₀x⟩ := rat_den_unity_is_nat k₀x' h₁k₀x h₂k₀x

  let k₁ := k₀x - k₀


  have hkq₂ : (k₀ * x).den = 1 := by
    obtain ⟨hq₁, hq₂⟩ := hkq₁
    apply hq₁

  have hk₂ : 0 < k₀ := by
    apply Nat.zero_lt_of_ne_zero
    unfold S at hkq₁
    simp_all

  have hx₃ : x < 2 := by nlinarith

  -- Then k₁ = k₀ * (x - 1) < k₀ * (2 - 1) = k₀.
  have asdfasdf :=
    calc ↑k₁
      _= ↑k₀x - ↑k₀ := by sorry
      _= k₀ * x - k₀  := by sorry
      _= k₀ * (x - 1) := by ring
      _< k₀ * (2 - 1) := by rel [hx₃]
      _= k₀ := by ring

  -- So, k₁ ∈ ℕ and k₁ < k₀ → k₁ ∉ S because k₀ is the least element of S.
  -- need to prove k₁ has den = 1.

  have hhk₂ : 0 ≤ k₁ := by aesop

  have hc₂ : ¬ (k₁ ∈ S) := by
    obtain ⟨hj₁, hj₂⟩ := hk
    simp [lowerBounds] at hj₂
    intro hj₃
    have hj₄ := @hj₂ k₁
    contrapose hj₄
    push_neg
    constructor
    · exact hj₃
    · --
      have hx₅ : 1 < x := by nlinarith
      have hh₀ : 0 < k₁ := by
        aesop
        omega
      dsimp [k₁]
      aesop

  -- But, x*k₁ = k₀*x^2 - x*k₀ = 2*k₀ - x*k₀ = k₀-k₁ ∈ ℕ → k₁ ∈ S

  -- ! k₁ < k₀
  -- ! k₁ ∈ S
  -- ! k₀ is not the least element in S.
  have hcc₁ : k₀x = k₀x' := by aesop

  have hc₄ : k₁ ∈ S := by

    have hh₁ : x * k₁ = k₀ - k₁ := by
      dsimp [k₁]
      have : x * ↑(k₁) = x * ↑(k₀x - k₀) := by dsimp [k₁]
      have : x * ↑(k₀x - k₀) = x * ↑k₀x - x * ↑k₀ := by
        rw [hk₀x]
        rw [mul_eq_mul_left_iff] at this
        cases this with
        | inr h => rw [h]; ring
        | inl h =>
          · --
            rw [←h]
            have he₁ :=
              calc x * k₀x' - x * ↑k₀
                _= x * (k₀x' - ↑k₀) := by ring
            rw [he₁]
            rw [mul_eq_mul_left_iff]
            left
            dsimp [k₁]
            dsimp [k₀x']
            have he₂ :=
              calc ↑k₀ * x - ↑k₀
                _= ↑k₀ * (x - 1) := by ring
            rw [he₂]
            have he₃ : ↑(k₀x - k₀) = (↑k₀x) - (↑k₀) := by aesop


    -- need to establish that k₁ in S.

    -- have hkx : (x * k₁).den = 1 := by
    --   dsimp [k₁]



  -- this establishes that x*k₁ is a natural number
  -- therefore k₁ ∈ S, by dsimp S and some figuring.
  contradiction















end q_no_lubp








end Lecture3
