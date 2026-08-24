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
# Tao's Optimization constant 62a / The Lindelöf exponent for the Riemann zeta function

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 62a](https://teorth.github.io/optimizationproblems/constants/62a.html)
- [HL1923] Hardy, G. H.; Littlewood, J. E. "The approximate functional equation in the theory of
  the zeta-function, with applications to the divisor problems of Dirichlet and Piltz."
  Proceedings of the London Mathematical Society 21 (1923), 39–74.
- [Bou2017] Bourgain, J. "Decoupling, exponential sums and the Riemann zeta function." Journal of
  the American Mathematical Society 30 (2017), 205–224.
- [Har2019] Harper, A. J. Survey of growth bounds for $\zeta$, 2019.
-/

open Filter Complex

namespace Constant62a

/-- **Tao's Optimization constant 62a / The Lindelöf exponent for the Riemann zeta function**:
the infimal $\theta \ge 0$ with $|\zeta(1/2 + it)| \ll_\varepsilon (1 + |t|)^{\theta + \varepsilon}$
for every $\varepsilon > 0$. -/
@[optimization_constant "62a"]
noncomputable def C62a : ℝ :=
  sInf {θ : ℝ | 0 ≤ θ ∧ ∀ ε > 0,
    (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[atTop] fun t : ℝ => (1 + |t|) ^ (θ + ε)}

/-- The trivial lower bound $0$. -/
@[category research solved, AMS 11]
theorem c62a_lower_bound : 0 ≤ C62a := by
  sorry

/-- The best known upper bound $13/84$, proven by Bourgain in [Bou2017]. The classical
convexity bound is $1/4$ and Hardy-Littlewood [HL1923] gave $1/6$. -/
@[category research solved, AMS 11]
theorem c62a_upper_bound : C62a ≤ 13 / 84 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ico_c62a : answer(sorry) ∈ Set.Ico C62a (13 / 84) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ioc_c62a : answer(sorry) ∈ Set.Ioc 0 C62a := by
  sorry

/-- What is the exact value of the constant? The **Lindelöf hypothesis** asserts that it is
$0$ [Har2019]. -/
@[category research open, AMS 11]
theorem c62a_eq : C62a = answer(sorry) := by
  sorry

end Constant62a
