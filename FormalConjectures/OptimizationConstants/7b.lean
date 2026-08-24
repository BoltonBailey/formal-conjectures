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
# Tao's Optimization constant 7b / The irrationality measure of $\Gamma(1/4)$

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 7b](https://teorth.github.io/optimizationproblems/constants/7b.html)
- [Bru2002] Bruiltet, S. "D'une mesure d'approximation simultanée à une mesure d'irrationalité:
  le cas de $\Gamma(1/4)$ et $\Gamma(1/3)$." Acta Arithmetica 104 (2002), 243–281.
- [Zud2004] Zudilin, W. "Approximations to $q$-logarithms and $q$-dilogarithms, with
  applications to $q$-zeta values." 2004.

The predicate `LiouvilleWith p x` of Mathlib says that $|x - m/n| < C/n^p$ has infinitely many
solutions for some constant $C$, so the irrationality measure of $x$ is the supremum of the
exponents $p$ with `LiouvilleWith p x`.
-/

open Real

namespace Constant7b

/-- The **irrationality measure** of a real number $x$: the supremum of the exponents $p$ for
which $|x - m/n| < C/n^p$ has infinitely many solutions, for some constant $C$. -/
noncomputable def irrationalityMeasure (x : ℝ) : ℝ := sSup {p : ℝ | LiouvilleWith p x}

/-- **Tao's Optimization constant 7b / The irrationality measure of $\Gamma(1/4)$**. -/
@[optimization_constant "7b"]
noncomputable def C7b : ℝ := irrationalityMeasure (Real.Gamma (1 / 4))

/-- The lower bound $2$, which holds for every irrational number by Dirichlet's approximation
theorem. -/
@[category research solved, AMS 11]
theorem c7b_lower_bound : 2 ≤ C7b := by
  sorry

/-- The best known upper bound $10^{143}$, proven by Bruiltet in [Bru2002]. -/
@[category research solved, AMS 11]
theorem c7b_upper_bound : C7b ≤ 10 ^ (143 : ℕ) := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ico_c7b : answer(sorry) ∈ Set.Ico C7b (10 ^ (143 : ℕ)) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ioc_c7b : answer(sorry) ∈ Set.Ioc 2 C7b := by
  sorry

/-- What is the exact value of the constant? The gap between the proven bounds $2$ and
$10^{143}$ reflects how weak the current methods are for special constants. -/
@[category research open, AMS 11]
theorem c7b_eq : C7b = answer(sorry) := by
  sorry

end Constant7b
