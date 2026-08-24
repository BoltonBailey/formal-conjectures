/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjecturesUtil
import FormalConjectures.Wikipedia.KomlosConjecture

/-!
# Tao's Optimization constant 24a / The Komlós discrepancy constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 24a](https://teorth.github.io/optimizationproblems/constants/24a.html)
- [Ban1998] Banaszczyk, W. "Balancing vectors and Gaussian measures of $n$-dimensional convex
  bodies." Random Structures & Algorithms 12 (1998), 351–360.
- [Kun2023] Kunisky, D. "A lower bound for the Komlós conjecture constant." 2023.
- [BJ2025] Bansal, N.; Jiang, H. "Improved bounds for the Komlós problem." 2025.

The Komlós conjecture is formalised in `FormalConjectures.Wikipedia.KomlosConjecture`.
-/

open scoped ENNReal

namespace Constant24a

/-- The dimension-$n$ Komlós discrepancy $K_n$: the supremum of $\min_{x \in \{-1,1\}^n}
\|Ax\|_\infty$ over real $n \times n$ matrices $A$ whose columns have Euclidean norm at
most $1$. -/
noncomputable def K (n : ℕ) : ℝ≥0∞ :=
  ⨆ A : {A : Matrix (Fin n) (Fin n) ℝ // ∀ j, ∑ i, (A i j) ^ 2 ≤ 1},
    ENNReal.ofReal (sInf {r : ℝ | ∃ x : Fin n → ℝ, (∀ j, x j = 1 ∨ x j = -1) ∧
      r = ⨆ i, |∑ j, (A : Matrix (Fin n) (Fin n) ℝ) i j * x j|})

/-- **Tao's Optimization constant 24a / The Komlós discrepancy constant**:
$\sup_{n \ge 1} K_n$. The **Komlós conjecture** asserts that this constant is finite. -/
@[optimization_constant "24a"]
noncomputable def C24a : ℝ≥0∞ := ⨆ n : ℕ, K n

/-- The best known lower bound $1 + \sqrt{2}$, proven by Kunisky in [Kun2023]. -/
@[category research solved, AMS 5 11]
theorem c24a_lower_bound : ENNReal.ofReal (1 + Real.sqrt 2) ≤ C24a := by
  sorry

/-- The trivial upper bound: no finite upper bound is known, since the finiteness of the
constant is exactly the Komlós conjecture. The best known bound on $K_n$ is
$\widetilde{O}(\log^{1/4} n)$ [BJ2025], improving on Banaszczyk's $O(\sqrt{\log n})$
[Ban1998]. -/
@[category research solved, AMS 5 11]
theorem c24a_upper_bound : C24a ≤ ⊤ :=
  le_top

/-- **The Komlós conjecture**: is the constant finite? -/
@[category research open, AMS 5 11]
theorem c24a_ne_top : C24a ≠ ⊤ := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5 11]
theorem mem_Ioc_c24a : answer(sorry) ∈ Set.Ioc (ENNReal.ofReal (1 + Real.sqrt 2)) C24a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c24a_eq : C24a = answer(sorry) := by
  sorry

end Constant24a
