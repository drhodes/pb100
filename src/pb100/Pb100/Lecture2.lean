import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic
import Mathlib.Init.Logic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.ModEq
import Mathlib.Tactic.ModCases
--import Mathlib.Init.Set

/-

https://leanprover-community.github.io/mathematics_in_lean/C04_Sets_and_Functions.html

When using lean, set theory does not play the same roll as usual.

-/

section images


#check Set.image

-- def image {β : Type v} (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}

def Image {α β : Type} (C: Set α) (f: α → β) := {f x | x ∈ C}
def InvImage {α β : Type} (D: Set β) (f: α → β) := { x | f x ∈ D}


def inj (A: Set α) (B: Set β) (f: α→β) :=
def sur (A: Set α) (B: Set β) (f: α→β) := ∀y ∈ B, ∃x ∈ A, f x ∈ B ∧ f x = y
def bij (A: Set α) (B: Set β) (f: α→β) := inj A B f ∧ sur A B f

def card_eq (A: Set α) (B: Set β) := ∃ f, bij A B f
def card_le (A: Set α) (B: Set β) := ∃ f, inj A B f
def card_lt (A: Set α) (B: Set β) := ∃ f, inj A B f ∧ ¬ bij A B f




#check Injective


end images


namespace card₁

def CardEq1 (f : α → β) := Bijective f

def ex (s : Set ℕ) : Set ℕ := {2*n | n : s}

-- example : CardEq1 ex41 := by
--   dsimp [CardEq1, Bijective]
--   constructor

end card₁

namespace card₂

-- def CardEq2 (X: Set α) (Y: Set β) := ∃ f: α → β, Bijective f

end card₂

namespace card₁

-- def Injection (X: Set α) (Y: Set β) := ∃ f:(X → Y), f X = f Y → X = Y that
-- doesn't work because X and Y are different types, so f can't be apply to both.


-- def SetCardinalityEq (X: Set α) (Y: Set β) := ∃ f: X → Y, Bijective f



-- example : SetCardinalityEq {n | n : ℕ} {2*n | n : ℕ} := by
--   dsimp [SetCardinalityEq] --, Bijective, Injective, Surjective]
--   sorry
-- ⊢ ∃ f, Bijective f

-- where f should have type: { x // ∃ n, n = x } → { x // ∃ n, 2 * n = x }
-- but I don't know what to do with that
-- the only interesting part at the core is (λ n => 2*n)

-- Declare f as a function from some type α to some type β
variable (f : Set α → Set β)
variable (C D : Set α)

example : f (C ∪ D) = f (C) ∪ f (D) := by
  ext y
  constructor
  · intro h
    simp at h
    obtain ⟨x, ⟨hx, hfx⟩⟩ := h
    cases hx
    · left
      exact ⟨x, hx, hfx⟩
    · right
      exact ⟨x, hx, hfx⟩
  · intro h
    simp
    cases h
    · obtain ⟨x, hx, hfx⟩ := h
      exact ⟨x, Or.inl hx, hfx⟩
    · obtain ⟨x, hx, hfx⟩ := h
      exact ⟨x, Or.inr hx, hfx⟩




end card₃


namespace card₄

variable {α : Type _}
variable {x y z: Set α}

#check Set.card_ne_eq


example : x ⊆ x := by

  intro a
  sorry

example (h1 : x ⊆ y) (h2 : y ⊆ z) : x ⊆ z := by
  intro a
  sorry

example (h1 : x ⊆ y) (h2 : y ⊆ x) : x = y := by
  funext a
  apply propext
  sorry



end card₄

namespace card₅
open Function

-- If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
-- forward along `f` to make a subset `(f S) : Set Y` of `Y`. The definition
-- of `(f S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.



  -- {y : Y | ∃ x : X, x ∈ S ∧ f x = y}

end card₅






/-

theorem lft_inv_imp_inj (g: Y→X) (f: X→Y): lft_inv g f → inj f := by
  intro hlinv
  dsimp [lft_inv] at *
  unfold inj
  intro a b hf
  have ha := hlinv
  have hb := hlinv
  specialize ha a
  specialize hb b
  rw [hf] at ha
  rw [←ha]
  rw [hb]
  done

-- right inverse implies surjection
theorem rht_inv_imp_sur (f: X→Y) (g: Y→X) : rht_inv f g → sur f := by
  intro h
  unfold rht_inv at h
  unfold sur
  intro b
  use (g b)
  apply h
  done

-- inverse implies bijection
theorem inv_imp_bij (f: X→Y) : (∃g:Y→X, inv f g) → bij f := by
  intro h
  obtain ⟨g, ifg⟩ := h
  unfold bij
  unfold inv at ifg
  obtain ⟨linv, rinv⟩ := ifg
  constructor
  · exact lft_inv_imp_inj g f linv
  · exact rht_inv_imp_sur f g rinv
  done


-- surjection implies right inverse
theorem sur_imp_rht_inv (f: S→T) : sur f → ∃g: T→S, rht_inv f g := by
  intro h
  unfold sur at h
  choose g hg using h
  unfold rht_inv
  use g
  done

-- https://www.cs.cornell.edu/courses/cs2800/2017fa/lectures/lec13-inverses.html
-- Claim: if f:A→B is injective and A≠∅, then f has a left-inverse.

-- Proof: Suppose f:A→B is injective.
-- Note that since A≠∅, there exists some a0∈A.
-- Let g:B→A be defined as follows.
-- Given b∈B, if b=f(a) for some a in A, then let g(b):=a.
--   If b is not in the image of f, then define g(b):=a0.

-- g is a left-inverse of f.
-- In other words, g∘f=id.
-- In other words, ∀a∈A, g(f(a))=a.
-- To see this, choose an arbitrary a∈A.
-- Then f(a) is in the image of f,
-- so by definition of g,
-- we have g(f(a))=a′ for some a′ satisfying f(a′)=f(a).
-- But since f is injective, we know a′=a, which is what we wanted to prove.

theorem inj_imp_lft_inv (f: A→B) : inj f → ∃g: B→A, lft_inv g f := by
  intro h
  unfold inj at h
  unfold lft_inv
  sorry


-- bijection implies left inverse
theorem bij_imp_lft_inv (f: X→Y) (h: bij f): ∃ g, lft_inv g f := by
  dsimp [bij, lft_inv] at *
  obtain ⟨hif, hsf⟩ := h
  apply sur_imp_rht_inv at hsf
  apply inj_imp_lft_inv at hif
  obtain ⟨gl, hl⟩ := hif
  use gl
  intro x
  unfold lft_inv at hl
  specialize hl x
  exact hl
  done

-- bijection implies right inverse
theorem bij_imp_rht_inv (f: X→Y) (h: bij f): ∃ g, rht_inv f g := by
  dsimp [bij] at *
  apply sur_imp_rht_inv
  obtain ⟨_, hsf⟩ := h
  exact hsf



theorem bij_imp_inv (f: X→Y) : bij f → (∃g:Y→X, inv f g) := by
  intro h
  have hl := bij_imp_lft_inv f h
  obtain ⟨g, hg⟩ := hl
  have hbg : bij g := by
    unfold bij
    apply And.intro
    unfold inj
    intro y₁ y₂ gy₁₂
    unfold lft_inv at hg






    --   let x₂ = g y₂
    --   have hg₁ := hg
    --   specialize hg₁ x₁
    --   rw [←x₁] at hg₁


    -- · unfold lft_inv at hg
    --   unfold sur
    --   intro x₁
    --   use (f x₁)
    --   apply hg


  have hr := bij_imp_rht_inv g


  sorry


def set_func (f: A→B) := {(a, b) : A × B | f a = b}






-- https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/formalisingmathematics.pdf
-- Classical choose

-- https://raw.githubusercontent.com/blanchette/logical_verification_2023/main/hitchhikers_guide.pdf
-- page 165 The Axiom of Choice

#check Exists.intro (1:ℕ)

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h


example : ∃ y : ℕ, y > 0 := by
  have h : 1 > 0 := Nat.zero_lt_succ 0
  choose n hn using (Exists.intro 1 h)
  use n

example : ∃ x : ℕ, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

-- example : True := by
--   have h1: Exists.intro (x:ℕ)

-- def inj (f: X→Y) := ∀a:X, ∀b:X, f a = f b → a = b

example (h: inj (id: ℕ→ℕ)): id x = (x:ℕ) := by
  unfold inj at h
  apply h
  norm_num

/-- If a function f is injective then f has left inverse g, such that g (f x) = x -/
theorem inj_imp_lft_inv (f: S→T) : inj f → ∃g: T→S, lft_inv g f := by
  intro hf
  unfold inj at *
  unfold lft_inv
  -- stuck!
  sorry

/-- If a function f is bijective then it has an overall inverse -/
theorem bij_imp_inv (f: X→Y) : bij f → (∃g:Y→X, inv f g) := by
  intro h
  unfold bij at h
  obtain ⟨fi, fs⟩ := h
  unfold sur at fs
  unfold inj at fi
  unfold inv
  sorry


theorem bij_imp_cnv_bij (f: X→Y) : ∃g:Y→X, bij f → bij g := by
  constructor
  intro h
  apply inv_imp_bij
  unfold bij at h
  obtain ⟨fi, fs⟩ := h
  unfold inv
  use f
  sorry

-/


-- theorem card_eq_symm: ∀ x y: Type, (card_eq x y) → (card_eq y x) := by
--   sorry

/-
theorem card_eq_imp: ∀ x y: Type, (card_eq x y) → (card_eq y x) := by
  intro X Y hab
  dsimp [card_eq] at hab
  obtain ⟨func, hf⟩ := hab
  unfold card_eq
  have h1: ∃g:Y→X, inv func g := by
    apply bij_imp_inv
    exact hf

  have h2: ∃h:Y→X, sur h := by
    unfold sur
    obtain ⟨g, hg⟩ := h1
    use g
    intro a
    use (func a)
    unfold inv at hg
    obtain ⟨gf, fg⟩ := hg
    have hgf : g (func a) = (g ∘ func) a := by
      rw [gf]
    rw [hgf, gf]; rfl

  have h3: ∃h:Y→X, inj h := by
    unfold inj
    unfold inv at h1
    obtain ⟨gf', fg'⟩ := h1
    obtain ⟨gf, fg⟩ := fg'
    sorry
  sorry


-/

-- theorem card_eq_symm: ∀ x y: Type, (card_eq x y) ↔ (card_eq y x) := by
--   apply Iff.

-- lemma inj_trans (x1 y1: α) (x2 y2: β): (inj f x1 y1 ∧ inj g x2 y2) → (∃j:α→γ, inj j x1 y1) := by
--   norm_num
--   intros h1 h2
--   use (g ∘ f)
--   unfold inj at *
--   intro h3
--   apply h1
--   aesop?
--   -- need inverse.

--def card_eq := ∃ f', bij A B f'
-- def card_le := ∃ f', inj f' x y
-- def card_lt := ∃ f', inj f ∧ ¬ bij f

/-
theorem card_eq_trans: card_eq A B ∧ card_eq B C → card_eq A C := by
  norm_num
  intro h1 h2
  unfold card_eq at *
  unfold bij at *
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  let h := λ x => g (f x)
  use h
  obtain ⟨h1, h2⟩ := hf
  obtain ⟨h3, h4⟩ := hg
  constructor
  unfold inj
  intro x hx y hy
  norm_num
  intro hxc hyc hxy
  sorry


-/
