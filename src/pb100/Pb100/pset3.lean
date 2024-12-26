import Mathlib

namespace Pset3


-- based on pset found at the following link:
-- https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/resources/mit18_100af20_hw3/

-- Exercises given with a numbering are from Basic Analysis: Introduction to
-- Real Analysis (Vol I) by J. Lebl.

example (a b c : ℝ) : a - b < c ↔ a < c + b := by exact sub_lt_iff_lt_add
example (a : Prop) : a ∨ ¬ a := by exact Classical.em a






end Pset3
