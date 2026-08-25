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
- [Per1947] Perkal, Julian. "Sur la subdivision des ensembles en parties de diamètre inférieur."
  Colloquium Mathematicum 1 (1947), 45.
- [Gru1957] Grünbaum, Branko. "A simple proof of Borsuk’s conjecture in three dimensions."
  Proceedings of the Cambridge Philosophical Society 53 (1957), 776–778.
- [Jen2018] Jenrich, Thomas. "On the counterexamples to Borsuk’s conjecture by Kahn and Kalai."
  Preprint (2018). [arXiv:1809.09612](https://arxiv.org/abs/1809.09612)
- [N1994] Nilli, A. "On Borsuk’s problem." In: "Jerusalem Combinatorics ’93", Contemporary
  Mathematics 178, Amer. Math. Soc. (1994), 209–210.
- [R1997] Raigorodskii, A. M. "On the dimension in Borsuk’s problem." Russian Mathematical Surveys
  52 (1997), no. 6, 1324–1325. [MathNet](https://www.mathnet.ru/eng/rm912)
- [Wei2000] Weißbach, Bernulf. "Sets with large Borsuk number." Beiträge zur Algebra und Geometrie
  41 (2000), 417–423.
- [Hin2002] Hinrichs, Aicke. "Spherical codes and Borsuk's conjecture." Discrete Mathematics 243
  (2002), 253–256.
- [Pik2002] Pikhurko, Oleg. "Borsuk's conjecture fails in dimensions 321 and 322." Preprint (2002).
  [arXiv:math/0202112](https://arxiv.org/abs/math/0202112)
- [HR2003] Hinrichs, Aicke; Richter, Christian. "New sets with large Borsuk numbers." Discrete
  Mathematics 270 (2003), no. 1–3, 137–147. DOI:
  [10.1016/S0012-365X(02)00833-6](https://doi.org/10.1016/S0012-365X(02)00833-6)
- [Bon2014] Bondarenko, Andriy. "On Borsuk’s conjecture for two-distance sets." Discrete &
  Computational Geometry 51 (2014), no. 3, 509–515. Preprint:
  [arXiv:1305.2584](https://arxiv.org/abs/1305.2584)

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

/-- Lower bound from [Per1947], [Egg1955], [Gru1957] (1947, 1955, 1957). Borsuk’s conjecture is true
for $n\le 3$. After the $63$-dimensional construction, the first possible failing dimension remains
open for $4\le n \le 62$. [WX2022-lb-nle3] -/
@[category research solved, AMS 52]
theorem c28a_lower_bound_per1947_egg1955_gru1957 : 4 ≤ C28a := by
  sorry

/-- Upper bound from [KK1993], [Jen2018] (1993, 1809). First counterexamples in high dimension
(Kahn–Kalai); see Jen2018 for detailed discussion of the construction. [KK1993-ub-1325]
[Jen2018-jen2018-detail] -/
@[category research solved, AMS 52]
theorem c28a_upper_bound_kk1993_jen2018 : C28a ≤ 1325 := by
  sorry

/-- Upper bound from [N1994] (1994). Improves the explicit counterexample dimension.
[Bon2014-ub-improvements] -/
@[category research solved, AMS 52]
theorem c28a_upper_bound_n1994 : C28a ≤ 946 := by
  sorry

/-- Upper bound from [R1997] (1997). [Bon2014-ub-improvements] -/
@[category research solved, AMS 52]
theorem c28a_upper_bound_r1997 : C28a ≤ 561 := by
  sorry

/-- Upper bound from [Wei2000] (2000). [Bon2014-ub-improvements] -/
@[category research solved, AMS 52]
theorem c28a_upper_bound_wei2000 : C28a ≤ 560 := by
  sorry

/-- Upper bound from [Hin2002] (2002). Spherical-code based construction. [Bon2014-ub-improvements]
[Pik2002-hin2002-spherical] -/
@[category research solved, AMS 52]
theorem c28a_upper_bound_hin2002 : C28a ≤ 323 := by
  sorry

/-- Upper bound from [Pik2002] (2002). Gives counterexamples in dimensions $321$ and $322$.
[Bon2014-ub-improvements] [Pik2002-ub-321-322] -/
@[category research solved, AMS 52]
theorem c28a_upper_bound_pik2002 : C28a ≤ 321 := by
  sorry

/-- Upper bound from [HR2003] (2003). [Bon2014-ub-298] -/
@[category research solved, AMS 52]
theorem c28a_upper_bound_hr2003 : C28a ≤ 298 := by
  sorry

/-- Upper bound from [Bon2014] (2014). Two-distance counterexample (416 points on $S^{64}\subset
\mathbb{R}^{65}$); cannot be partitioned into $83$ smaller-diameter sets (so needs $\ge 84$).
[Bon2014-ub-65] -/
@[category research solved, AMS 52]
theorem c28a_upper_bound_bon2014 : C28a ≤ 65 := by
  sorry

/-- Upper bound from [JB2014] (2014). A 352-point two-distance subset giving a counterexample in
$\mathbb{R}^{64}$; cannot be partitioned into $70$ smaller-diameter sets (so needs $\ge 71$).
[JB2014-ub-64] -/
@[category research solved, AMS 52]
theorem c28a_upper_bound_jb2014 : C28a ≤ 64 := by
  sorry

/-- Upper bound from [Gri2026] (2026). Current best: a $321$-point subset of $\mathbb{R}^{63}$ whose
smaller-diameter subsets have size at most $5$, so at least $65>64$ parts are required. -/
@[category research solved, AMS 52]
theorem c28a_upper_bound_gri2026 : C28a ≤ 63 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 52]
theorem c28a_eq : answer(sorry) = C28a := by
  sorry

end Constant28a
