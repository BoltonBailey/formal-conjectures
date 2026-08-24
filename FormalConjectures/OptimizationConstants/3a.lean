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
# Tao's Optimization constant 3a / The Gyarmati-Hennecart-Ruzsa sum-difference constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 3a](https://teorth.github.io/optimizationproblems/constants/3a.html)
- [Ru96] Ruzsa, I. Z. "Sums of finite sets." Number Theory (New York, 1991–1995), Springer
  (1996), 281–293.
- [GHR2007] Gyarmati, K.; Hennecart, F.; Ruzsa, I. Z. "Sums and differences of finite sets."
  Functiones et Approximatio 37 (2007), 175–186.
- [GGSWT2025] Georgiev, B.; Gómez-Serrano, J.; Tao, T.; Wagner, A. Z. "Mathematical exploration
  and discovery at scale." [arXiv:2511.02864](https://arxiv.org/abs/2511.02864)
-/

open scoped Pointwise Finset

namespace Constant3a

/-- **Tao's Optimization constant 3a / The Gyarmati-Hennecart-Ruzsa sum-difference constant**:
the largest constant $c$ for which there are arbitrarily large finite sets $A, B$ of integers
with $|A + B| \ll |A|$ and $|A - B| \gg |A + B|^c$. -/
@[optimization_constant "3a"]
noncomputable def C3a : ℝ :=
  sSup {c : ℝ | ∃ K > (0 : ℝ), ∃ κ > (0 : ℝ), ∀ N : ℕ, ∃ A B : Finset ℤ,
    N ≤ #A ∧ (#(A + B) : ℝ) ≤ K * #A ∧ κ * (#(A + B) : ℝ) ^ c ≤ #(A - B)}

/-- The best known lower bound $1.1584$, found with AlphaEvolve in [GGSWT2025]. The first
non-trivial bound $2 - \log 6 / \log 7 = 1.0792\ldots$ is due to Ruzsa [Ru96]. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound : 1.1584 ≤ C3a := by
  sorry

/-- The best known upper bound $4/3$, proven by Gyarmati-Hennecart-Ruzsa in [GHR2007]. -/
@[category research solved, AMS 5 11]
theorem c3a_upper_bound : C3a ≤ 4 / 3 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 5 11]
theorem mem_Ico_c3a : answer(sorry) ∈ Set.Ico C3a (4 / 3) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5 11]
theorem mem_Ioc_c3a : answer(sorry) ∈ Set.Ioc 1.1584 C3a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c3a_eq : C3a = answer(sorry) := by
  sorry

end Constant3a
