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
import FormalConjectures.ErdosProblems.«508»

/-!
# Tao's Optimization constant 27a / The chromatic number of the plane

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 27a](https://teorth.github.io/optimizationproblems/constants/27a.html)
- [Had1945] Hadwiger, H. "Überdeckung des euklidischen Raumes durch kongruente Mengen."
  Portugaliae Mathematica 4 (1945), 238–242.
- [MM1961] Moser, L.; Moser, W. "Solution to Problem 10." Canadian Mathematical Bulletin 4
  (1961), 187–189.
- [deG2018] de Grey, Aubrey D. N. J. "The chromatic number of the plane is at least 5."
  Geombinatorics 28 (2018), 18–31. [arXiv:1804.02385](https://arxiv.org/abs/1804.02385)
- [CR2017] Cranston, Daniel W.; Rabern, Landon. "The fractional chromatic number of the plane."
  Combinatorica 37 (2017), no. 5, 837–861. [arXiv:1501.01647](https://arxiv.org/abs/1501.01647)

The problem is formalised in `FormalConjectures.ErdosProblems.«508»`.
-/

open scoped EuclideanGeometry

namespace Constant27a

/-- **Tao's Optimization constant 27a / The chromatic number of the plane**:
the smallest number of colours needed to colour $\mathbb{R}^2$ so that no two points at distance
$1$ receive the same colour, i.e. the chromatic number of the unit-distance graph on the plane
(the Hadwiger-Nelson problem). -/
@[optimization_constant "27a"]
noncomputable def C27a : ℕ∞ :=
  SimpleGraph.chromaticNumber (SimpleGraph.UnitDistancePlaneGraph Set.univ)

/-- Trivial lower bound. An equilateral triangle of side length $1$ forces three colors. -/
@[category research solved, AMS 5 52]
theorem c27a_lower_bound_trivial : 3 ≤ C27a := by
  exact Erdos508.HadwigerNelsonAtLeastThree

/-- Lower bound from [MM1961] (1961). Moser spindle: a $7$-vertex unit-distance graph with chromatic
number $4$. -/
@[category research solved, AMS 5 52]
theorem c27a_lower_bound_mm1961 : 4 ≤ C27a := by
  sorry

/-- Lower bound from [deG2018] (1804). First proof that $\chi(\mathbb R^{2})\ge 5$, via an explicit
finite unit-distance graph. -/
@[category research solved, AMS 5 52]
theorem c27a_lower_bound_deg2018 : 5 ≤ C27a := by
  sorry

/-- Upper bound from [Had1945], [CR2017] (1945, 2017). A periodic $7$-coloring obtained from a
tiling of the plane by small regular hexagons (historically attributed to Isbell, 1950). -/
@[category research solved, AMS 5 52]
theorem c27a_upper_bound_had1945_cr2017 : C27a ≤ 7 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 52]
theorem c27a_eq : answer(sorry) = C27a := by
  sorry

end Constant27a
