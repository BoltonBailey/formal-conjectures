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

/-- The best known lower bound $5$, proven by de Grey in [deG2018]. -/
@[category research solved, AMS 5 52]
theorem c27a_lower_bound : 5 ≤ C27a :=
  Erdos508.HadwigerNelsonAtLeastFive

/-- The best known upper bound $7$, coming from a periodic colouring of a hexagonal tiling
[Had1945]. -/
@[category research solved, AMS 5 52]
theorem c27a_upper_bound : C27a ≤ 7 :=
  Erdos508.HadwigerNelsonAtMostSeven

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 52]
theorem c27a_eq : C27a = answer(sorry) := by
  sorry

end Constant27a
