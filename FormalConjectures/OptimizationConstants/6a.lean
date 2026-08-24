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
import FormalConjectures.Wikipedia.UnionClosed

/-!
# Tao's Optimization constant 6a / The union-closed sets constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 6a](https://teorth.github.io/optimizationproblems/constants/6a.html)
- [F1995] Frankl, P. "Extremal set systems." Handbook of Combinatorics, Vol. 2 (1995),
  1293–1329. The conjecture that the constant equals $1/2$ is due to Frankl (1976).
- [G2022] Gilmer, J. "A constant lower bound for the union-closed sets conjecture."
  [arXiv:2211.09055](https://arxiv.org/abs/2211.09055)
- [L2023] Liu, L. "Improved bounds for the union-closed sets conjecture."
  [arXiv:2311.05737](https://arxiv.org/abs/2311.05737)

The union-closed condition is formalised in `FormalConjectures.Wikipedia.UnionClosed` as
`UnionClosed.IsUnionClosed`.
-/

open Finset

namespace Constant6a

/-- **Tao's Optimization constant 6a / The union-closed sets constant**:
the largest constant $C$ such that every union-closed family of sets, other than the family
containing only the empty set, has an element belonging to at least a $C$ fraction of the sets. -/
@[optimization_constant "6a"]
noncomputable def C6a : ℝ :=
  sSup {c : ℝ | ∀ (n : ℕ) (A : Finset (Finset (Fin n))), A.Nonempty → A ≠ {∅} →
    UnionClosed.IsUnionClosed A → ∃ i : Fin n, c * #A ≤ #{x ∈ A | i ∈ x}}

/-- The best known lower bound $0.38271$, proven by Liu in [L2023]. Gilmer [G2022] gave the
first constant lower bound. -/
@[category research solved, AMS 5]
theorem c6a_lower_bound : 0.38271 ≤ C6a := by
  sorry

/-- The upper bound $1/2$, which is attained by the power set of a singleton. Frankl conjectured
in 1976 that this is the exact value [F1995]. -/
@[category research solved, AMS 5]
theorem c6a_upper_bound : C6a ≤ 1 / 2 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5]
theorem mem_Ioc_c6a : answer(sorry) ∈ Set.Ioc 0.38271 C6a := by
  sorry

/-- What is the exact value of the constant? The **union-closed sets conjecture** of Frankl
asserts that it is $1/2$. -/
@[category research open, AMS 5]
theorem c6a_eq : C6a = answer(sorry) := by
  sorry

end Constant6a
