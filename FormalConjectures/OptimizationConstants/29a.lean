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
# Tao's Optimization constant 29a / The kissing number in dimension 5

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 29a](https://teorth.github.io/optimizationproblems/constants/29a.html)
- [KZ1873] Korkine, A.; Zolotareff, G. "Sur les formes quadratiques positives." Mathematische
  Annalen 6 (1873), 366–389. The $D_5$ root system gives $40$ points.
- [BV2008] Bachoc, C.; Vallentin, F. "New upper bounds for kissing numbers from semidefinite
  programming." Journal of the American Mathematical Society 21 (2008), 909–924.
- [MV2009] Mittelmann, H. D.; Vallentin, F. "High accuracy semidefinite programming bounds for
  kissing numbers." Experimental Mathematics 19 (2010), 175–179.
-/

open EuclideanSpace Metric
open scoped Finset

namespace Constant29a

/-- **Tao's Optimization constant 29a / The kissing number in dimension 5**:
the largest number of unit spheres that can touch a central unit sphere in $\mathbb{R}^5$
without overlapping. Equivalently, this is the largest size of a spherical code on $S^4$ with
pairwise inner products at most $1/2$. -/
@[optimization_constant "29a"]
noncomputable def C29a : ℕ :=
  sSup {n : ℕ | ∃ C : Finset (EuclideanSpace ℝ (Fin 5)), #C = n ∧
    (∀ x ∈ C, ‖x‖ = 1) ∧ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → inner ℝ x y ≤ (1 / 2 : ℝ)}

/-- The best known lower bound $40$, achieved by the $D_5$ root system [KZ1873]. -/
@[category research solved, AMS 11 52]
theorem c29a_lower_bound : 40 ≤ C29a := by
  sorry

/-- The best known upper bound $44$, proven by Mittelmann-Vallentin in [MV2009] using
semidefinite programming, refining [BV2008]. -/
@[category research solved, AMS 11 52]
theorem c29a_upper_bound : C29a ≤ 44 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11 52]
theorem mem_Ico_c29a : answer(sorry) ∈ Set.Ico C29a 44 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11 52]
theorem mem_Ioc_c29a : answer(sorry) ∈ Set.Ioc 40 C29a := by
  sorry

/-- What is the exact value of the constant? It is widely believed to be $40$. Dimension $5$ is
the smallest dimension in which the kissing number is unknown. -/
@[category research open, AMS 11 52]
theorem c29a_eq : C29a = answer(sorry) := by
  sorry

end Constant29a
