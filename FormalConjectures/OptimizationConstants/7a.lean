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
# Tao's Optimization constant 7a / The irrationality measure of $\pi$

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 7a](https://teorth.github.io/optimizationproblems/constants/7a.html)
- [D1842] Dirichlet, G. L. "Verallgemeinerung eines Satzes aus der Lehre von den
  Kettenbrüchen nebst einigen Anwendungen auf die Theorie der Zahlen." 1842.
- [M1953] Mahler, K. "On the approximation of $\pi$." Indagationes Mathematicae 15 (1953),
  30–42.
- [S2008] Salikhov, V. K. "On the irrationality measure of $\pi$." Russian Mathematical Surveys
  63 (2008), 570–572.
- [ZZ2020] Zeilberger, D.; Zudilin, W. "The irrationality measure of $\pi$ is at most
  7.103205334137\ldots" Moscow Journal of Combinatorics and Number Theory 9 (2020), 407–419.
  [arXiv:1912.06345](https://arxiv.org/abs/1912.06345)

The predicate `LiouvilleWith p x` of Mathlib says that $|x - m/n| < C/n^p$ has infinitely many
solutions for some constant $C$, so the irrationality measure of $x$ is the supremum of the
exponents $p$ with `LiouvilleWith p x`.
-/

open Real

namespace Constant7a

/-- The **irrationality measure** of a real number $x$: the supremum of the exponents $p$ for
which $|x - m/n| < C/n^p$ has infinitely many solutions, for some constant $C$. -/
noncomputable def irrationalityMeasure (x : ℝ) : ℝ := sSup {p : ℝ | LiouvilleWith p x}

/-- **Tao's Optimization constant 7a / The irrationality measure of $\pi$**. -/
@[optimization_constant "7a"]
noncomputable def C7a : ℝ := irrationalityMeasure π

/-- The lower bound $2$, which holds for every irrational number by Dirichlet's approximation
theorem [D1842]. -/
@[category research solved, AMS 11]
theorem c7a_lower_bound : 2 ≤ C7a := by
  sorry

/-- The best known upper bound $7.103205334137\ldots$, proven by Zeilberger-Zudilin
in [ZZ2020]. Mahler [M1953] gave the first finite bound, $42$. -/
@[category research solved, AMS 11]
theorem c7a_upper_bound : C7a ≤ 7.103205334137 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ico_c7a : answer(sorry) ∈ Set.Ico C7a 7.103205334137 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ioc_c7a : answer(sorry) ∈ Set.Ioc 2 C7a := by
  sorry

/-- What is the exact value of the constant? It is widely believed to be $2$, the value for
Lebesgue-almost every real number. -/
@[category research open, AMS 11]
theorem c7a_eq : C7a = answer(sorry) := by
  sorry

end Constant7a
