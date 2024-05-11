introducing this proposition, how to prove that this is true?

$$ (n^2 + n) = 2 \cdot \sum_{i=0}^n i $$

Here is the sum function that realizes the summation


``` { .python }
import Mathlib.Tactic
open Nat

def sum_to (n: ℕ): ℕ :=
  match n with
  | zero   => 0
  | succ m => n + sum_to m
```

Here is the proposition we need to prove.

```
def P(n) := (n^2 + n) = 2 * sum_to n
```

But first, we need to prove the following implication for any particular step
along the natural numbers. This does not come for free, it needs to be proved!

\[ P(m) \implies P(m+1) \]


```
lemma step : ∀m, P m → P (m + 1) := by    
```  

<input type="text" id="name" name="name"/>

```
lemma base : P 0 := by
```

<input type="text" id="name" name="name"/>
  

```
theorem sum_of_one_to_n : (∀n, P n) := by
```  

<input type="text" id="name" name="name"/>