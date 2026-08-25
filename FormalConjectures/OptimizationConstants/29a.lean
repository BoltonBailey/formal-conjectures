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
- [Cox1963] Coxeter, Harold Scott Macdonald. "An upper bound for the number of equal nonoverlapping
  spheres that can touch another of the same size." In: "Proc. Sympos. Pure Math." 7 (1963), 53–71.
- [OS1979] Odlyzko, A. M.; Sloane, N. J. A. "New bounds on the number of unit spheres that can touch
  a unit sphere in $n$ dimensions." Journal of Combinatorial Theory, Series A 26 (1979), 210–214.
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

/-- Trivial lower bound. Trivial construction via the cross polytope $\{\pm e_i\}_{i=1}^5\subset
S^4$. -/
@[category research solved, AMS 11 52]
theorem c29a_lower_bound_trivial : 10 ≤ C29a := by
  sorry

/-- Lower bound from [KZ1873] (1873). Achieved by the $D_5$ root system (40 points), giving a
kissing configuration of size $40$ in $\mathbb{R}^5$. [CR2024-lb-40-D5] -/
@[category research solved, AMS 11 52]
theorem c29a_lower_bound_kz1873 : 40 ≤ C29a := by
  sorry

/-- Upper bound from [Cox1963] (1963). Coxeter’s strongest bound in dimension $5$ (as summarized in
the survey literature). [BDM2012-ub-story-d5] -/
@[category research solved, AMS 11 52]
theorem c29a_upper_bound_cox1963 : C29a ≤ 48 := by
  sorry

/-- Upper bound from [OS1979] (1979). The bound $46.345$, which for the integer $C_{29a}$ means
$C_{29a} \le 46$. Improvement attributed to Odlyzko–Sloane (as summarized in the survey literature).
[BDM2012-ub-story-d5] -/
@[category research solved, AMS 11 52]
theorem c29a_upper_bound_os1979 : C29a ≤ 46 := by
  sorry

/-- Upper bound from [BV2008], [MV2009] (2008, 2010). Semidefinite-programming upper bound recorded
as the best “known upper bound” prior to the higher-accuracy SDP computations. -/
@[category research solved, AMS 11 52]
theorem c29a_upper_bound_bv2008_mv2009 : C29a ≤ 45 := by
  sorry

/-- Upper bound from [MV2009] (2010). [MV2009-range-40-44] -/
@[category research solved, AMS 11 52]
theorem c29a_upper_bound_mv2009 : C29a ≤ 44 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11 52]
theorem c29a_eq : answer(sorry) = C29a := by
  sorry

end Constant29a
