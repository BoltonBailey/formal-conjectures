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
# Tao's Optimization constant 13b / The Lebesgue universal covering constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 13b](https://teorth.github.io/optimizationproblems/constants/13b.html)
- [Pal1920] Pál, J. "Über ein elementares Variationsproblem." Danske Videnskabernes Selskab
  Mathematisk-fysiske Meddelelser III 2 (1920).
- [Elek1994] Elekes, G. Lower bounds for the universal cover problem, 1994.
- [BS2005] Brass, P.; Sharifi, M. "A lower bound for Lebesgue's universal cover problem."
  International Journal of Computational Geometry & Applications 15 (2005), 537–544.
- [Gib2018] Gibbs, P. "An upper bound for Lebesgue's covering problem."
  [arXiv:1810.10089](https://arxiv.org/abs/1810.10089)
-/

open MeasureTheory
open scoped EuclideanGeometry ENNReal

namespace Constant13b

/-- The convex planar sets of diameter $1$. -/
def UnitDiameterConvexSets : Set (Set ℝ²) := {s | Convex ℝ s ∧ Metric.diam s = 1}

/-- The convex universal covers: measurable convex sets that cover a congruent copy of every
convex planar set of diameter $1$. Congruences here include reflections. -/
def UniversalCovers : Set (Set ℝ²) :=
  {X | MeasurableSet X ∧ Convex ℝ X ∧ ∀ s ∈ UnitDiameterConvexSets,
    ∃ (e : ℝ² ≃ₗᵢ[ℝ] ℝ²) (v : ℝ²), s ⊆ (fun x => e x + v) '' X}

/-- **Tao's Optimization constant 13b / The Lebesgue universal covering constant**:
the infimal area of a convex planar set that covers a congruent copy of every convex planar set
of diameter $1$. -/
@[optimization_constant "13b"]
noncomputable def C13b : ℝ≥0∞ := sInf {v | ∃ X ∈ UniversalCovers, volume X = v}

/-- The best known lower bound $0.832$, proven by Brass-Sharifi in [BS2005] with a rigorous
computer-aided search. Elekes [Elek1994] gave $0.8271$. -/
@[category research solved, AMS 52]
theorem c13b_lower_bound : 0.832 ≤ C13b := by
  sorry

/-- The best known upper bound $0.8440935944$, proven by Gibbs in [Gib2018]. Pál's regular
hexagon [Pal1920] gives $\sqrt{3}/2$. -/
@[category research solved, AMS 52]
theorem c13b_upper_bound : C13b ≤ 0.8440935944 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ico_c13b : answer(sorry) ∈ Set.Ico C13b 0.8440935944 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ioc_c13b : answer(sorry) ∈ Set.Ioc 0.832 C13b := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 52]
theorem c13b_eq : C13b = answer(sorry) := by
  sorry

end Constant13b
