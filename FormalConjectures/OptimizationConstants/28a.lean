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
import FormalConjectures.ErdosProblems.«505»

/-!
# Tao's Optimization constant 28a / The smallest dimension in which Borsuk's conjecture fails

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 28a](https://teorth.github.io/optimizationproblems/constants/28a.html)
- [Egg1955] Eggleston, H. G. "Covering a three-dimensional set with sets of smaller diameter."
  Journal of the London Mathematical Society 30 (1955), 11–24.
- [KK1993] Kahn, J.; Kalai, G. "A counterexample to Borsuk's conjecture." Bulletin of the
  American Mathematical Society 29 (1993), 60–62.
- [JB2014] Jenrich, T.; Brouwer, A. E. "A 64-dimensional counterexample to Borsuk's conjecture."
  Electronic Journal of Combinatorics 21 (2014), #P4.29.
- [Gri2026] Griego, 2026: a $321$-point subset of $\mathbb{R}^{63}$ giving a counterexample in
  dimension $63$.

Borsuk's conjecture is formalised in `FormalConjectures.ErdosProblems.«505»`.
-/

open Metric Set

namespace Constant28a

/-- **Tao's Optimization constant 28a / The smallest dimension in which Borsuk's conjecture
fails**: the smallest $n$ for which some bounded $S \subseteq \mathbb{R}^n$ of positive diameter
cannot be covered by $n + 1$ sets of strictly smaller diameter. -/
@[optimization_constant "28a"]
noncomputable def C28a : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ m : ℕ, n = m ∧ ∃ S : Set (EuclideanSpace ℝ (Fin m)),
    Bornology.IsBounded S ∧ 0 < diam S ∧
      ∀ F : Fin (m + 1) → Set (EuclideanSpace ℝ (Fin m)),
        S ⊆ ⋃ i, F i → ∃ i, diam S ≤ diam (F i)}

/-- The best known lower bound $4$: Borsuk's conjecture holds in dimensions at most $3$, the
case $n = 3$ being due to Eggleston [Egg1955]. -/
@[category research solved, AMS 52]
theorem c28a_lower_bound : 4 ≤ C28a := by
  sorry

/-- The best known upper bound $63$ [Gri2026]. The first counterexamples in high dimension are
due to Kahn-Kalai [KK1993]; dimension $64$ was reached by Jenrich-Brouwer [JB2014]. -/
@[category research solved, AMS 52]
theorem c28a_upper_bound : C28a ≤ 63 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ico_c28a : answer(sorry) ∈ Set.Ico C28a 63 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ioc_c28a : answer(sorry) ∈ Set.Ioc 4 C28a := by
  sorry

/-- What is the exact value of the constant? It is unknown for every dimension between $4$ and
$62$ whether Borsuk's conjecture holds. -/
@[category research open, AMS 52]
theorem c28a_eq : C28a = answer(sorry) := by
  sorry

end Constant28a
