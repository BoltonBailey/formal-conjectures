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

/-!
# Tao's Optimization constant 5b / Sidon set density inside (4,5) sets

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 5b](https://teorth.github.io/optimizationproblems/constants/5b.html)
- [GL95] Erdős, P.; Gyárfás, A.; Lehel, J. Sidon subsets of $(4,5)$-sets, 1995.
- [MT26] Improved bounds on Sidon subsets of $(4,5)$-sets, 2026.

Sidon sets are formalised in `FormalConjecturesForMathlib` as `IsSidon`.
-/

open scoped Finset

namespace Constant5b

/-- A finite set of reals is a **$(4,5)$-set** if every four-element subset determines at least
five distinct (unsigned, non-zero) differences. -/
def Is45Set (A : Finset ℝ) : Prop :=
  ∀ B ⊆ A, #B = 4 →
    5 ≤ #(((B ×ˢ B).filter fun p => p.1 ≠ p.2).image fun p => |p.1 - p.2|)

/-- **Tao's Optimization constant 5b / Sidon set density inside (4,5) sets**:
the largest constant $c$ such that every $(4,5)$-set of size $n$ contains a Sidon set of
cardinality at least $cn$. -/
@[optimization_constant "5b"]
noncomputable def C5b : ℝ :=
  sSup {c : ℝ | ∀ A : Finset ℝ, Is45Set A →
    ∃ S ⊆ A, IsSidon (S : Set ℝ) ∧ c * #A ≤ #S}

/-- Lower bound from [GL95] (1995). A short 2-colorability argument -/
@[category research solved, AMS 5 11]
theorem c5b_lower_bound_gl95_1 : 1 / 2 ≤ C5b := by
  sorry

/-- Lower bound from [GL95] (1995). -/
@[category research solved, AMS 5 11]
theorem c5b_lower_bound_gl95_2 : 1 / 2 + (1 / (141 * 76)) ≤ C5b := by
  sorry

/-- Lower bound from [MT26] (2026). -/
@[category research solved, AMS 5 11]
theorem c5b_lower_bound_mt26 : 9 / 17 ≤ C5b := by
  sorry

/-- Trivial upper bound. -/
@[category research solved, AMS 5 11]
theorem c5b_upper_bound_trivial : C5b ≤ 1 := by
  sorry

/-- Upper bound from [GL95] (1995). -/
@[category research solved, AMS 5 11]
theorem c5b_upper_bound_gl95 : C5b ≤ 3 / 5 := by
  sorry

/-- Upper bound from [MT26] (2026). -/
@[category research solved, AMS 5 11]
theorem c5b_upper_bound_mt26 : C5b ≤ 4 / 7 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c5b_eq : answer(sorry) = C5b := by
  sorry

end Constant5b
