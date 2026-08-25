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
- [Gri26] Max Grinsztajn. Code and certificate for a Ramsey upper bound below 3.792. GitHub
  repository, 2026. https://github.com/maaxgrin/ramsey-3792-bound

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

/-- Lower bound from [Erd1947] (1947). Introduces Erdős’ probabilistic method -/
@[category research solved, AMS 5]
theorem c17a_lower_bound_erd1947 : Real.sqrt 2 ≤ C17a := by
  sorry

/-- Upper bound from [ES1935] (1935). -/
@[category research solved, AMS 5]
theorem c17a_upper_bound_es1935 : C17a ≤ 4 := by
  sorry

/-- Upper bound from [CGMS2023] (2023). A simpler proof with $4 - 2^{-10}$ is also provided -/
@[category research solved, AMS 5]
theorem c17a_upper_bound_cgms2023 : C17a ≤ 4 - 2 ^ (-7 : ℤ) := by
  sorry

/-- Upper bound from [GNNW2024] (2024). Optimizes parameters in the [CGMS2023] approach -/
@[category research solved, AMS 5]
theorem c17a_upper_bound_gnnw2024 : C17a ≤ 4 * Real.exp (-0.14 / Real.exp 1) := by
  sorry

/-- Upper bound from [Gri26] (2026). Computer-assisted verification using Theorem 13 and Lemma 14 of
[GNNW2024] -/
@[category research solved, AMS 5]
theorem c17a_upper_bound_gri26 : C17a ≤ 3.791993699438612 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5]
theorem c17a_eq : answer(sorry) = C17a := by
  sorry

end Constant17a
