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
import FormalConjectures.Wikipedia.Hadamard

/-!
# Tao's Optimization constant 23a / The smallest unsolved instance of the Hadamard conjecture

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 23a](https://teorth.github.io/optimizationproblems/constants/23a.html)
- [CP2024] Ćustić, A.; Ponomarenko, V. Survey of known Hadamard matrix orders; the smallest
  order for which no Hadamard matrix is known is $668$.

Hadamard matrices are formalised in `FormalConjectures.Wikipedia.Hadamard` as
`Hadamard.IsHadamard`.
-/

namespace Constant23a

/-- **Tao's Optimization constant 23a / The smallest unsolved instance of the Hadamard
conjecture**: the smallest $n$ divisible by $4$ for which there is no Hadamard matrix of order
$n$, or $\infty$ if no such $n$ exists. The **Hadamard conjecture** asserts that it is
$\infty$. -/
@[optimization_constant "23a"]
noncomputable def C23a : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ k : ℕ, n = 4 * k ∧ ¬ ∃ M, Hadamard.IsHadamard (n := 4 * k) M}

/-- The best known lower bound $668$: every order $n < 668$ with $4 \mid n$ is known to admit a
Hadamard matrix [CP2024]. -/
@[category research solved, AMS 5 15]
theorem c23a_lower_bound : 668 ≤ C23a := by
  sorry

/-- The best known upper bound is the trivial bound $\infty$: no finite upper bound is known. -/
@[category research solved, AMS 5 15]
theorem c23a_upper_bound : C23a ≤ ⊤ :=
  le_top

/-- How can the lower bound be improved? -/
@[category research open, AMS 5 15]
theorem mem_Ioc_c23a : answer(sorry) ∈ Set.Ioc 668 C23a := by
  sorry

/-- What is the exact value of the constant? The **Hadamard conjecture** asserts that it is
$\infty$. -/
@[category research open, AMS 5 15]
theorem c23a_eq : C23a = answer(sorry) := by
  sorry

end Constant23a
