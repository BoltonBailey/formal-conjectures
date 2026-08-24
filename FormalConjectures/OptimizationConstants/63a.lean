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
# Tao's Optimization constant 63a / The Dirichlet divisor problem exponent

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 63a](https://teorth.github.io/optimizationproblems/constants/63a.html)
- [Hux2003] Huxley, M. N. "Exponential sums and lattice points III." Proceedings of the London
  Mathematical Society 87 (2003), 591–609.
- [Tsa2010] Tsang, K.-M. "Recent progress on the Dirichlet divisor problem and the mean square of
  the Riemann zeta-function." Science China Mathematics 53 (2010), 2561–2572.
-/

open Filter

namespace Constant63a

/-- The error term $\Delta(x) = \sum_{n \le x} d(n) - x(\log x + 2\gamma - 1)$ in the Dirichlet
divisor problem, where $d(n)$ is the number of divisors of $n$ and $\gamma$ is the
Euler-Mascheroni constant. -/
noncomputable def Δ (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) -
    x * (Real.log x + 2 * Real.eulerMascheroniConstant - 1)

/-- **Tao's Optimization constant 63a / The Dirichlet divisor problem exponent**:
the infimal $a \ge 0$ with $\Delta(x) = O(x^{a + \varepsilon})$ for every $\varepsilon > 0$. -/
@[optimization_constant "63a"]
noncomputable def C63a : ℝ :=
  sInf {a : ℝ | 0 ≤ a ∧ ∀ ε > 0, Δ =O[atTop] fun x : ℝ => x ^ (a + ε)}

/-- The lower bound $1/4$, which follows from Hardy's omega result [Tsa2010]. -/
@[category research solved, AMS 11]
theorem c63a_lower_bound : 1 / 4 ≤ C63a := by
  sorry

/-- The best known upper bound $131/416$, proven by Huxley in [Hux2003]. -/
@[category research solved, AMS 11]
theorem c63a_upper_bound : C63a ≤ 131 / 416 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ico_c63a : answer(sorry) ∈ Set.Ico C63a (131 / 416) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ioc_c63a : answer(sorry) ∈ Set.Ioc (1 / 4) C63a := by
  sorry

/-- What is the exact value of the constant? It is conjectured to be $1/4$ [Tsa2010]. -/
@[category research open, AMS 11]
theorem c63a_eq : C63a = answer(sorry) := by
  sorry

end Constant63a
