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

/-- Trivial lower bound. Trivial from the definition $C_{62a}\ge 0$. -/
@[category research solved, AMS 11]
theorem c62a_lower_bound_trivial : 0 ≤ C62a := by
  sorry

/-- Upper bound from [Har2019] (2019). Convexity bound. [Har2019-convexity-1-4] -/
@[category research solved, AMS 11]
theorem c62a_upper_bound_har2019_1 : C62a ≤ 1 / 4 := by
  sorry

/-- Upper bound from [Har2019] (2019). Hardy-Littlewood bound. [Har2019-hl-1-6] -/
@[category research solved, AMS 11]
theorem c62a_upper_bound_har2019_2 : C62a ≤ 1 / 6 := by
  sorry

/-- Upper bound from [Bou2017] (2017). Bourgain's pointwise bound for $\lvert\zeta(1/2+it)\rvert$.
[Bou2017-13-84] -/
@[category research solved, AMS 11]
theorem c62a_upper_bound_bou2017 : C62a ≤ 13 / 84 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c62a_eq : answer(sorry) = C62a := by
  sorry

end Constant62a
