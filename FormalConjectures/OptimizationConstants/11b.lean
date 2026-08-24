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
import FormalConjectures.Mathoverflow.«10799»

/-!
# Tao's Optimization constant 11b / The Hamming cube isoperimetric exponent

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 11b](https://teorth.github.io/optimizationproblems/constants/11b.html)
- [Har1966] Harper, L. H. "Optimal numberings and isoperimetric problems on graphs." Journal of
  Combinatorial Theory 1 (1966), 385–393.
- [KP2020] Kahn, J.; Park, J. "An isoperimetric inequality for the Hamming cube and some
  consequences." Proceedings of the American Mathematical Society 148 (2020), 4213–4224.
- [BIM2023] Beltran, J.; Ivanisvili, P.; Madrid, J. "On sharp isoperimetric inequalities on the
  hypercube." 2023.
- [DIR2024] Durcik, P.; Ivanisvili, P.; Roos, J. "A sharp isoperimetric inequality on the
  hypercube." 2024.
- [DIRX2026] Durcik, P.; Ivanisvili, P.; Roos, J.; Xie, X. Solution of the problem, establishing
  $\beta = 1/2$, 2026.

The boundary count $h_A$ is formalised in `FormalConjectures.Mathoverflow.«10799»` as
`Mathoverflow10799.boundaryCount`.
-/

open Finset

namespace Constant11b

/-- The function $h_A$ on the Hamming cube: for $x \in A$ it is the number of neighbours of $x$
outside $A$, and it is $0$ for $x \notin A$. -/
def h (n : ℕ) (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) : ℕ :=
  if S ∈ F then Mathoverflow10799.boundaryCount n F S else 0

/-- **Tao's Optimization constant 11b / The critical exponent for the isoperimetric inequality
on the Hamming cube**: the infimum of the exponents $\beta > 0$ such that
$\mathbb{E}\,h_A(x)^\beta \ge 1/2$ for every $n$ and every $A \subseteq \{-1, 1\}^n$ with
$|A| = 2^{n-1}$, where $x$ is uniform on the cube. -/
@[optimization_constant "11b"]
noncomputable def C11b : ℝ :=
  sInf {β : ℝ | 0 < β ∧ ∀ (n : ℕ) (F : Finset (Finset (Fin n))), #F = 2 ^ (n - 1) →
    (1 / 2 : ℝ) ≤ (1 / 2 ^ n : ℝ) * ∑ S : Finset (Fin n), (h n F S : ℝ) ^ β}

/-- The lower bound $1/2$, proven by Beltran-Ivanisvili-Madrid in [BIM2023]: for every
$\beta < 1/2$, Hamming ball examples make $\mathbb{E}\,h_A(x)^\beta$ arbitrarily small. -/
@[category research solved, AMS 5 52 60]
theorem c11b_lower_bound : 1 / 2 ≤ C11b := by
  sorry

/-- The upper bound $1/2$, proven by Durcik-Ivanisvili-Roos-Xie in [DIRX2026]. The classical
edge isoperimetric inequality [Har1966] gives $1$; intermediate improvements are due to
Kahn-Park [KP2020] and Durcik-Ivanisvili-Roos [DIR2024]. -/
@[category research solved, AMS 5 52 60]
theorem c11b_upper_bound : C11b ≤ 1 / 2 := by
  sorry

/-- The exact value of the constant is $1/2$, established in [DIRX2026]. -/
@[category research solved, AMS 5 52 60]
theorem c11b_eq : C11b = 1 / 2 :=
  le_antisymm c11b_upper_bound c11b_lower_bound

end Constant11b
