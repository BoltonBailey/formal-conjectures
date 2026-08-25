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
import FormalConjectures.Wikipedia.GaussCircleProblem

/-!
# Tao's Optimization constant 64a / The Gauss circle problem exponent

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 64a](https://teorth.github.io/optimizationproblems/constants/64a.html)
- [Hux2003] Huxley, M. N. "Exponential sums and lattice points III." Proceedings of the London
  Mathematical Society 87 (2003), 591–609.
- [Har1915] Hardy, G. H. "On the expression of a number as the sum of two squares." Quarterly
  Journal of Mathematics 46 (1915), 263–283. Hardy conjectured the optimal exponent $1/2$.

The lattice point counting error term is formalised in
`FormalConjectures.Wikipedia.GaussCircleProblem` as `GaussCircleProblem.E`.
-/

open Filter

namespace Constant64a

/-- **Tao's Optimization constant 64a / The Gauss circle problem exponent**:
the smallest exponent $\theta$ such that the number $N(t)$ of lattice points in the disc of
radius $t$ satisfies $N(t) = \pi t^2 + O(t^{\theta + \varepsilon})$ for every
$\varepsilon > 0$. -/
@[optimization_constant "64a"]
noncomputable def C64a : ℝ :=
  sInf {θ : ℝ | ∀ ε > 0, GaussCircleProblem.E =O[atTop] fun t : ℝ => t ^ (θ + ε)}

/-- Trivial lower bound. Trivial from the definition $C_{64}\ge 0$. -/
@[category research solved, AMS 11]
theorem c64a_lower_bound_trivial : 0 ≤ C64a := by
  sorry

/-- Trivial upper bound. Trivial bound $N(t)=\pi t^2+O(t)$. -/
@[category research solved, AMS 11]
theorem c64a_upper_bound_trivial : C64a ≤ 1 := by
  sorry

/-- Upper bound from [Hux2003] (2003). Huxley's bound (long-standing record). [CRM2023-ub-131-208]
-/
@[category research solved, AMS 11]
theorem c64a_upper_bound_hux2003 : C64a ≤ 131 / 208 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c64a_eq : answer(sorry) = C64a := by
  sorry

end Constant64a
