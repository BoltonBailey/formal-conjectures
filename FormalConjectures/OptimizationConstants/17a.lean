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
import FormalConjectures.Wikipedia.RamseyNumbers

/-!
# Tao's Optimization constant 17a / The exponential growth constant for diagonal Ramsey numbers

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 17a](https://teorth.github.io/optimizationproblems/constants/17a.html)
- [ES1935] Erdős, P.; Szekeres, G. "A combinatorial problem in geometry." Compositio Mathematica
  2 (1935), 463–470.
- [Erd1947] Erdős, P. "Some remarks on the theory of graphs." Bulletin of the American
  Mathematical Society 53 (1947), 292–294.
- [CGMS2023] Campos, M.; Griffiths, S.; Morris, R.; Sahasrabudhe, J. "An exponential improvement
  for diagonal Ramsey." [arXiv:2303.09521](https://arxiv.org/abs/2303.09521)
- [GNNW2024] Gupta, P.; Ndiaye, N.; Norin, S.; Wei, L. "Optimizing the CGMS upper bound on Ramsey
  numbers." [arXiv:2407.19026](https://arxiv.org/abs/2407.19026)

Ramsey numbers are formalised in `FormalConjectures.Wikipedia.RamseyNumbers` as
`RamseyNumbers.graphRamseyNumber`.
-/

open Filter

namespace Constant17a

/-- **Tao's Optimization constant 17a / The exponential growth constant for diagonal Ramsey
numbers**: the limit of $R(k)^{1/k}$, where $R(k)$ is the diagonal Ramsey number. The existence
of the limit is itself open, so we take a `limsup`. -/
@[optimization_constant "17a"]
noncomputable def C17a : ℝ :=
  limsup (fun k : ℕ => (RamseyNumbers.graphRamseyNumber k k : ℝ) ^ ((k : ℝ)⁻¹)) atTop

/-- The best known lower bound $\sqrt{2}$, proven by Erdős in [Erd1947] with the probabilistic
method. -/
@[category research solved, AMS 5]
theorem c17a_lower_bound : Real.sqrt 2 ≤ C17a := by
  sorry

/-- The best known upper bound $4e^{-0.14/e} = 3.7992027396\ldots$, proven by
Gupta-Ndiaye-Norin-Wei in [GNNW2024] by optimising the parameters of the
Campos-Griffiths-Morris-Sahasrabudhe argument [CGMS2023]. The classical bound $4$ is due to
Erdős-Szekeres [ES1935]. -/
@[category research solved, AMS 5]
theorem c17a_upper_bound : C17a ≤ 4 * Real.exp (-0.14 / Real.exp 1) := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 5]
theorem mem_Ico_c17a : answer(sorry) ∈ Set.Ico C17a (4 * Real.exp (-0.14 / Real.exp 1)) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5]
theorem mem_Ioc_c17a : answer(sorry) ∈ Set.Ioc (Real.sqrt 2) C17a := by
  sorry

/-- What is the exact value of the constant? Even the existence of the limit is open. -/
@[category research open, AMS 5]
theorem c17a_eq : C17a = answer(sorry) := by
  sorry

end Constant17a
