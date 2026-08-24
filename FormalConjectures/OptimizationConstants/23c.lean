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
# Tao's Optimization constant 23c / The asymptotic counting exponent for partial Hadamard matrices

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 23c](https://teorth.github.io/optimizationproblems/constants/23c.html)
- [DL2010] de Launey, W.; Levin, D. A. "A Fourier-analytic approach to counting partial Hadamard
  matrices." Cryptography and Communications 2 (2010), 307–334.
- [Can2011] Canfield, E. R. Unpublished improvement to the quartic regime, 2011.
- [Davis2026] Davis, ... Counting partial Hadamard matrices in the cubic regime, 2026.
-/

open scoped Real

namespace Constant23c

/-- The number $N_{n,t}$ of $n \times t$ **partial Hadamard matrices**: matrices with entries in
$\{\pm 1\}$ whose rows are pairwise orthogonal. -/
noncomputable def N (n t : ℕ) : ℕ :=
  Nat.card {M : Matrix (Fin n) (Fin t) ℝ //
    (∀ i j, M i j = 1 ∨ M i j = -1) ∧ ∀ i k, i ≠ k → ∑ j, M i j * M k j = 0}

/-- The main term $A_{n,4t} = 2^{4nt + (n-1)^2}(8\pi t)^{-n(n-1)/4}$. -/
noncomputable def mainTerm (n t : ℕ) : ℝ :=
  2 ^ (4 * n * t + (n - 1) ^ 2) * (8 * π * t) ^ (-(n * (n - 1) : ℝ) / 4)

/-- **Tao's Optimization constant 23c / The asymptotic counting exponent for partial Hadamard
matrices**: the smallest admissible exponent $\alpha \ge 1$ for which $N_{n,4t}$ admits a
uniform asymptotic formula throughout the regime $t / n^\alpha \to \infty$. -/
@[optimization_constant "23c"]
noncomputable def C23c : ℝ :=
  sInf {α : ℝ | 1 ≤ α ∧ ∀ ε > (0 : ℝ), ∃ T : ℝ, ∀ n t : ℕ,
    2 ≤ n → 1 ≤ t →
    T * (n : ℝ) ^ α ≤ t → |(N n (4 * t) : ℝ) / mainTerm n (4 * t) - 1| ≤ ε}

/-- The lower bound $1$: for $\alpha < 1$ the regime still includes widths with $4t < n$, where
no $n \times 4t$ partial Hadamard matrix exists [DL2010]. -/
@[category research solved, AMS 5 15]
theorem c23c_lower_bound : 1 ≤ C23c := by
  sorry

/-- The best known upper bound $3$, proven in [Davis2026]: the asymptotic holds for
$t / n^3 \to \infty$, and a non-vanishing correction survives at $t = \Theta n^3$, so the
asymptotics change at the cubic scale. Canfield [Can2011] had $4$. -/
@[category research solved, AMS 5 15]
theorem c23c_upper_bound : C23c ≤ 3 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 5 15]
theorem mem_Ico_c23c : answer(sorry) ∈ Set.Ico C23c 3 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5 15]
theorem mem_Ioc_c23c : answer(sorry) ∈ Set.Ioc 1 C23c := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 15]
theorem c23c_eq : C23c = answer(sorry) := by
  sorry

end Constant23c
