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
import FormalConjectures.ErdosProblems.«36»

/-!
# Tao's Optimization constant 1b / The Erdős minimum overlap constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 1b](https://teorth.github.io/optimizationproblems/constants/1b.html)
- [E1955] Erdős, P. "Problems and results in additive number theory." Colloque sur la Théorie des
  Nombres, Bruxelles, 1955, 127–137 (1956).
- [H2016] Haugland, J. K. "The minimum overlap problem revisited."
  [arXiv:1609.08000](https://arxiv.org/abs/1609.08000)
- [W2022] White, E. P. "Erdős' minimum overlap problem."
  [arXiv:2201.05704](https://arxiv.org/abs/2201.05704)

The teorth database states the constant in its equivalent continuous form, as the largest $C$
with $\sup_{x \in [-2, 2]} \int_{-1}^1 f(t)g(x + t)\,dt \ge C$ for all non-negative
$f, g : [-1, 1] \to [0, 1]$ with $f + g = 1$ and $\int f = 1$. Here we use the original discrete
form, via the counting function `Erdos36.M` of `FormalConjectures.ErdosProblems.«36»`.

A further, currently unpublished, upper bound of $0.380868$ was announced in 2026.
-/

open Filter

namespace Constant1b

/-- **Tao's Optimization constant 1b / The Erdős minimum overlap constant**:
the limit of $M(n)/n$, where $M(n)$ is the least possible maximum number of representations of
an integer as $a - b$, over all splittings of $\{1, \ldots, 2n\}$ into two sets $A$, $B$ of
equal size. The limit is known to exist; we take a `limsup` so that the definition does not
presuppose this. -/
@[optimization_constant "1b"]
noncomputable def C1b : ℝ := limsup (fun n : ℕ => (Erdos36.M n : ℝ) / n) atTop

/-- The best known lower bound $0.379005$, proven by White in [W2022]. -/
@[category research solved, AMS 5 11]
theorem c1b_lower_bound : 0.379005 ≤ C1b := by
  sorry

/-- The best published upper bound $0.380927$, proven by Haugland in [H2016]. -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound : C1b ≤ 0.380927 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 5 11]
theorem mem_Ico_c1b : answer(sorry) ∈ Set.Ico C1b 0.380927 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5 11]
theorem mem_Ioc_c1b : answer(sorry) ∈ Set.Ioc 0.379005 C1b := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c1b_eq : C1b = answer(sorry) := by
  sorry

end Constant1b
