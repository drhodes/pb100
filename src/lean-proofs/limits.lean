import Mathlib.Tactic
import Mathlib.Tactic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Data.Real.NNReal


def btwn (a b c: ℝ) := a < b ∧ b < c


variable (x: ℝ)

def lim_right   (f: ℝ → ℝ) (a: ℝ) (L: ℝ) := ∀ε>0, ∃δ>0, btwn a x (a + δ) → |f x - L| < ε
def lim_left    (f: ℝ → ℝ) (a: ℝ) (R: ℝ) := ∀ε>0, ∃δ>0, btwn (a - δ) x a → |f x - R| < ε
def lim_overall (f: ℝ → ℝ) (a: ℝ) (L: ℝ) := (lim_left x f a L) ∧ (lim_right x f a L)


def f1: ℝ → ℝ := λx ↦ x



-- def continuous_aap (f: ℝ → ℝ) (a: ℝ) :=
--   lim_overall x f a (f a) ∧







--def myabs (y: ℝ): ℝ := if x < 0 then -x else x


lemma exl1 : lim_left x f1 0 0 := by
  unfold lim_left
  norm_num
  intro ε h
  use ε
  unfold btwn
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
  unfold btwn
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
  unfold btwn
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
  unfold btwn
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
