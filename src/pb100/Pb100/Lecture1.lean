import Mathlib.Tactic
import Mathlib.Tactic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.EReal


def inj (A: Set α) (B: Set β) (f: α→β) := ∀x ∈ A, ∀y ∈ A, (f x ∈ B) ∧ (f y ∈ B) ∧ f x = f y → x = y
def sur (A: Set α) (B: Set β) (f: α→β) := ∀y ∈ B, ∃x ∈ A, f x ∈ B ∧ f x = y
def bij (A: Set α) (B: Set β) (f: α→β) := inj A B f ∧ sur A B f

def card_eq (A: Set α) (B: Set β) := ∃ f, bij A B f
def card_le (A: Set α) (B: Set β) := ∃ f, inj A B f
def card_lt (A: Set α) (B: Set β) := ∃ f, inj A B f ∧ ¬ bij A B f

-- idea try using functor.
def f₁ (n:ℤ) : ℚ := n / (n+1)
def S₁ : Set ℤ := {n | n : ℕ}

#check Functor.map f₁ S₁

example : card_eq {n | n : ℕ} {n | n : ℕ} := by
  unfold card_eq
  use id
  unfold bij
  tauto

-- again, without tauto
example : card_eq {n | n : ℕ} {n | n : ℕ} := by
  unfold card_eq
  use id
  unfold bij

  constructor
  · --
    dsimp [inj]
    intro x _ y _ h
    obtain ⟨_, _, h₃⟩ := h
    exact h₃
  · --
    dsimp [sur]
    intro y hy
    refine ⟨?_, ?_, ?_⟩
    · exact y
    · exact hy
    · constructor
      · exact hy
      · rfl




example : card_eq {n | n : ℕ} {2*n | n : ℕ} := by
  unfold card_eq
  use λ n => 2 * n
  unfold bij
  constructor
  · -- injective
    dsimp [inj]
    intro x hx y hy h₁
    obtain ⟨h₂, h₃, h₄⟩ := h₁
    linarith
  · -- surj
    dsimp [sur]
    intro y hy
    obtain ⟨m, hm⟩ := hy
    use m
    refine ⟨?_, ?_, ?_⟩
    · use m
    · use m
    · exact hm


example : card_eq {n | n : ℤ} {2*n - 1 | n : ℤ} := by
  unfold card_eq
  use λ n => 2 * n - 1
  unfold bij
  constructor
  · -- injective
    dsimp [inj]
    intro x hx y hy h₁
    obtain ⟨h₂, h₃, h₄⟩ := h₁
    calc x
      _= 2*x - 1 + 1 - x := by ring
      _= 2*y - 1 + 1 - x := by rw [h₄]
      _= 2*y - x := by ring
    linarith

  · -- surj
    dsimp [sur]
    intro y hy
    obtain ⟨m, hm⟩ := hy
    use m
    refine ⟨?_, ?_, ?_⟩
    · use m
    · use m
    · exact hm


lemma part1 (q: ℚ) (h₁: 0 < q) (h₂: q.den = 1) (h₃: q ≠ 1) : by
  have hn : q.num.toNat ≠ 0 := by aesop
  have h₄ := Nat.prod_primeFactorsList q.num.toNat


  sorry



example : card_eq {q : ℚ | ∃ q : ℚ, q > 0} {n | n : ℕ} := by
  sorry


  constructor
  · -- injective
    dsimp [inj]
    intro x hx y hy hs
    obtain ⟨h₁, h₂, h₃⟩ :=  hs


  · done


variable (x: ℝ)

def squeezed (l r: ℝ) := l < x ∧ x < r

def lim_right   (f: ℝ → ℝ) (a: ℝ) (L: ℝ) :=
  ∀ε>0, ∃δ>0, squeezed x a (a+δ) → |f x - L| < ε

def lim_left    (f: ℝ → ℝ) (a: ℝ) (R: ℝ) :=
  ∀ε>0, ∃δ>0, ((a - δ) < x ∧ x < a) → |f x - R| < ε

def lim_overall (f: ℝ → ℝ) (a: ℝ) (L: ℝ) := (lim_left x f a L) ∧ (lim_right x f a L)

def continuous_at_a_point (f: ℝ → ℝ) (a: ℝ) := lim_overall x f a (f a)

def f1 (x: ℝ) := x

example: continuous_at_a_point x f1 0  := by
  unfold continuous_at_a_point
  unfold lim_overall
  apply And.intro
  unfold lim_left
  norm_num
  intro ε h
  use ε
  apply And.intro
  exact h
  norm_num
  intro h1
  intro h2
  have h3: f1 0 = 0 := by rfl
  have h4: f1 x = x := by rfl
  rw [h3, h4]
  norm_num
  have h5: |x| = -x := by exact abs_of_neg h2
  rw [h5]
  linarith
  --
  unfold lim_right
  intro ε h1
  norm_num
  use ε
  apply And.intro
  exact h1
  intro h2 h3
  have h4: f1 0 = 0 := by rfl
  have h5: f1 x = x := by rfl
  rw [h4, h5]
  norm_num
  have h6: |x| = x := by exact abs_of_pos h2
  rw [h6]
  exact h3
  done




theorem lt_abs_swap (a b: ℝ) (hb: b < 0) : a < b → |b| < |a| := by
  intro h
  let c := -a
  let d := -b
  have h1 : a = -c := by ring
  have h2 : b = -d := by ring
  rw [h1, h2]
  have h3 : 0 < d := by linarith
  have h4 : 0 < c := by linarith
  norm_num
  rw [abs_of_pos h3]
  rw [abs_of_pos h4]
  exact neg_lt_neg h
  done


lemma lim_2_left : lim_left x f1 2 (f1 2) := by
  unfold lim_left
  norm_num
  intro ε h
  use (f1 ε)
  apply And.intro
  exact h
  --
  norm_num
  intro h1 h2
  unfold f1 at *
  have h3: -ε < (x-2) := by linarith
  have h4: x - 2 < 0 := by linarith
  have h6: |x-2| < |-ε| := by
    exact lt_abs_swap (-ε) (x - 2) h4 h3
  norm_num at h6
  have h7: |ε| = ε := by exact abs_of_pos h
  rw [h7] at h6
  exact h6
  done

lemma lim_2_right : lim_right x f1 2 (f1 2) := by
  unfold lim_right
  intro ε h1
  use ε
  apply And.intro
  exact h1
  --
  norm_num
  intro h2 h3
  unfold f1
  have h4: x - 2 > 0 := by exact sub_pos.mpr h2
  rw [abs_of_pos h4]
  linarith
  done


example: continuous_at_a_point x f1 2  := by
  unfold continuous_at_a_point
  unfold lim_overall
  apply And.intro
  apply lim_2_left
  apply lim_2_right
  done











--def myabs (y: ℝ): ℝ := if x < 0 then -x else x



lemma exl1 : lim_left x f1 0 0 := by
  unfold lim_left
  norm_num
  intro ε h
  use ε
  norm_num
  apply And.intro
  exact h
  intro h1 h2
  have h3 : -x < ε := by
    linarith
  unfold f1
  have h4 : |x| = -x := by
    exact abs_of_neg h2
  rw [h4]
  exact h3
  done

lemma exr1 : lim_right x f1 0 0 := by
  unfold lim_right
  norm_num
  intro ε h
  use ε
  apply And.intro
  exact h
  intro h1 h2
  unfold f1
  have h3 : |x| = x := by
    exact abs_of_pos h1
  rw [h3]
  exact h2
  done

example: lim_overall x f1 0 0 := by
  unfold lim_overall
  apply And.intro
  apply exl1
  apply exr1
  done

example: lim_right x Real.sqrt 0 0 := by
  unfold lim_right
  intro ε h
  use ε^2
  apply And.intro
  nlinarith
  norm_num
  intro h1
  intro h2
  have h3: Real.sqrt x < ε := by
    rw [←Real.sqrt_lt_sqrt_iff] at h2
    rw [Real.sqrt_sq] at h2
    exact h2
    norm_num
    rw [le_iff_lt_or_eq]
    left
    exact h
    rw [le_iff_lt_or_eq]
    left
    exact h1

  have h4: |Real.sqrt x| = Real.sqrt x := by
    apply NNReal.abs_eq
  rw [h4]
  exact h3
  done

def f2 (x: ℝ): ℝ := x + 2


example: lim_right x f2 0 2 := by
  unfold lim_right
  intro ε h
  use ε
  apply And.intro
  exact h
  norm_num
  intro h1
  intro left
  unfold f2
  norm_num
  have hx : |x| = x := by {
    exact abs_of_pos h1
  }
  rw [hx]
  exact left
  done



----

def P (n:ℕ) (c:ℤ) := (1+c)^(n+1) ≥ 1 + n*c


example: c ≥ -1 → ∀n, P (n+1) c := by
  intro hc n
  unfold P

  induction n with
  | zero => {
    norm_num
    nlinarith
  }
  | succ m ih => {
    rw [Nat.succ_eq_add_one]
    let k: ℤ := m
    -- identify this coercion,
    have hkm : (k + 1) = ↑(m + 1) := by rfl
    rw [←hkm] at ih
    have h2: (1 + c)*(1 + c) ^ (m + 2) ≥ (1+c)*(1 + (k + 1) * c) := by nlinarith

    calc (1 + c) ^ (m + 3)
      _ = (1 + c)*(1 + c) ^ (m + 2) := by ring
      _ ≥ (1 + c)*(1 + (k + 1) * c) := by exact h2
      _ =  1 + c + (1+c)*(k + 1) * c := by ring
      _ =  c^2 * k + c^2 + c * k + 2*c + 1 := by ring
      _ =  1 + (k + 2)*c + c^2 * k + c^2 := by ring
      _ ≥ 1 + (k + 2)*c := by nlinarith
    done
  }
