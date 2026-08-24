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
# Tao's Optimization constant 81a / Brun's constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 81a](https://teorth.github.io/optimizationproblems/constants/81a.html)
- [Bru1919] Brun, V. "La série $1/5 + 1/7 + 1/11 + 1/13 + \ldots$ où les dénominateurs sont
  nombres premiers jumeaux est convergente ou finie." Bulletin des Sciences Mathématiques 43
  (1919), 100–104 and 124–128.
- [PT2018] Platt, D.; Trudgian, T. "Improved bounds on Brun's constant." 2018.
  [arXiv:1803.01925](https://arxiv.org/abs/1803.01925)
-/

namespace Constant81a

/-- **Tao's Optimization constant 81a / Brun's constant**:
the sum of the reciprocals of the twin primes, $\sum_p (1/p + 1/(p+2))$ over primes $p$ such
that $p + 2$ is also prime. The series converges by Brun's theorem [Bru1919]. -/
@[optimization_constant "81a"]
noncomputable def C81a : ℝ :=
  ∑' p : {p : ℕ // p.Prime ∧ (p + 2).Prime}, ((p : ℝ)⁻¹ + ((p : ℝ) + 2)⁻¹)

/-- The best known lower bound $1.840503$, proven by Platt-Trudgian in [PT2018]. -/
@[category research solved, AMS 11]
theorem c81a_lower_bound : 1.840503 ≤ C81a := by
  sorry

/-- The best known unconditional upper bound $2.288513$, proven by Platt-Trudgian in [PT2018].
Assuming the generalised Riemann hypothesis, Dunn (2025) proved $C_{81a} < 2.1594$. -/
@[category research solved, AMS 11]
theorem c81a_upper_bound : C81a ≤ 2.288513 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ico_c81a : answer(sorry) ∈ Set.Ico C81a 2.288513 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ioc_c81a : answer(sorry) ∈ Set.Ioc 1.840503 C81a := by
  sorry

/-- What is the exact value of the constant? Numerical extrapolation suggests approximately
$1.902160583$, but this is not a rigorous bound. -/
@[category research open, AMS 11]
theorem c81a_eq : C81a = answer(sorry) := by
  sorry

end Constant81a
