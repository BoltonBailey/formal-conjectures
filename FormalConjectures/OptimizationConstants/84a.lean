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
import FormalConjectures.ErdosProblems.«90»

/-!
# Tao's Optimization constant 84a / The Erdős unit distance exponent

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 84a](https://teorth.github.io/optimizationproblems/constants/84a.html)
- [E1946] Erdős, P. "On sets of distances of $n$ points." American Mathematical Monthly 53 (1946),
  248–250.
- [SST1984] Spencer, J.; Szemerédi, E.; Trotter, W. T. "Unit distances in the Euclidean plane."
  Graph Theory and Combinatorics (1984), 293–303.
- [S2026] Sawin, W. "An explicit lower bound for the unit distance problem."
  [arXiv:2605.20579](https://arxiv.org/abs/2605.20579)
- [ABGLSSTWW2026] Alon, N.; Bloom, T. F.; Gowers, W. T.; Litt, D.; Sawin, W.; Shankar, A.;
  Tsimerman, J.; Wang, V.; Matchett Wood, M. "Remarks on the disproof of the unit distance
  conjecture." [arXiv:2605.20695](https://arxiv.org/abs/2605.20695)

The underlying counting function is formalised in `FormalConjectures.ErdosProblems.«90»` as
`Erdos90.maxUnitDistances`.
-/

open Filter

namespace Constant84a

/-- **Tao's Optimization constant 84a / The Erdős unit distance exponent**:
the exponent $\limsup_{n \to \infty} \frac{\log u(n)}{\log n}$, where $u(n)$ is the maximum
number of unit distances determined by $n$ points in the plane. -/
@[optimization_constant "84a"]
noncomputable def C84a : ℝ :=
  limsup (fun n : ℕ => Real.log (Erdos90.maxUnitDistances n) / Real.log n) atTop

/-- The best known lower bound $1.014114$, proven by Sawin in [S2026]. Erdős conjectured in
[E1946] that the exponent is $1$; this was disproved in 2026 [ABGLSSTWW2026]. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound : 1.014114 ≤ C84a := by
  sorry

/-- The best known upper bound $4/3$, proven by Spencer, Szemerédi and Trotter in [SST1984]
via the Szemerédi-Trotter incidence theorem. -/
@[category research solved, AMS 52]
theorem c84a_upper_bound : C84a ≤ 4 / 3 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ico_c84a : answer(sorry) ∈ Set.Ico C84a (4 / 3) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ioc_c84a : answer(sorry) ∈ Set.Ioc 1.014114 C84a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 52]
theorem c84a_eq : C84a = answer(sorry) := by
  sorry

end Constant84a
