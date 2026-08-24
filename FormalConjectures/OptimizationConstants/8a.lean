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
# Tao's Optimization constant 8a / The classical zero-free region constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 8a](https://teorth.github.io/optimizationproblems/constants/8a.html)
- [dlVP1899] de la Vallée Poussin, C.-J. "Sur la fonction $\zeta(s)$ de Riemann et le nombre des
  nombres premiers inférieurs à une limite donnée." Mém. Couronnés Acad. Roy. Belgique 59 (1899).
- [MTY2022] Mossinghoff, M. J.; Trudgian, T. S.; Yang, A. "Explicit zero-free regions for the
  Riemann zeta-function." 2022.
- [BTY2026] Bellotti, C.; Trudgian, T. S.; Yang, A. Improved explicit zero-free region, 2026.
-/

open Filter

namespace Constant8a

/-- **Tao's Optimization constant 8a / The classical zero-free region constant**:
the least $R$ such that the Riemann zeta function has no zero $\sigma + it$ with $|t| \ge 2$ and
$\sigma > 1 - \frac{1}{R \log |t|}$. -/
@[optimization_constant "8a"]
noncomputable def C8a : ℝ :=
  sInf {R : ℝ | 0 < R ∧ ∀ s : ℂ, riemannZeta s = 0 → 2 ≤ |s.im| →
    s.re ≤ 1 - 1 / (R * Real.log |s.im|)}

/-- The trivial lower bound $0$. Assuming the Riemann hypothesis the optimal value is
$2 / \log \gamma_1 \approx 0.755106$, where $\gamma_1$ is the ordinate of the lowest zero. -/
@[category research solved, AMS 11]
theorem c8a_lower_bound : 0 ≤ C8a := by
  sorry

/-- The best known upper bound $4.896$, proven by Bellotti-Trudgian-Yang in [BTY2026].
De la Vallée Poussin's original zero-free region [dlVP1899], which already gives the prime
number theorem, corresponds to $34.82$. -/
@[category research solved, AMS 11]
theorem c8a_upper_bound : C8a ≤ 4.896 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ico_c8a : answer(sorry) ∈ Set.Ico C8a 4.896 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ioc_c8a : answer(sorry) ∈ Set.Ioc 0 C8a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c8a_eq : C8a = answer(sorry) := by
  sorry

end Constant8a
