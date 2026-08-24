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
import FormalConjectures.Wikipedia.MoserWorm

/-!
# Tao's Optimization constant 13a / Moser's convex worm cover constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 13a](https://teorth.github.io/optimizationproblems/constants/13a.html)
- [Wan2006] Wang, Wei. "An improved upper bound for the worm problem." Acta Mathematica Sinica
  49 (2006), no. 4, 835–846.
- [KPS2013] Khandhawit, Tirasan; Pagonakis, Dimitrios; Sriswasdi, Sira. "Lower bound for convex
  hull area and universal cover problems." International Journal of Computational Geometry &
  Applications 23 (2013), no. 3, 197–212. [arXiv:1101.5638](https://arxiv.org/abs/1101.5638)
- [PW2021] Panraksa, Chatchawan; Wichiramala, Wacharin. "Wetzel's sector covers unit arcs."
  Periodica Mathematica Hungarica 82 (2021), 213–222.

Worms and worm covers are formalised in `FormalConjectures.Wikipedia.MoserWorm`.
-/

open MeasureTheory
open scoped ENNReal

namespace Constant13a

/-- **Tao's Optimization constant 13a / Moser's convex worm cover constant**:
the infimal area of a convex planar domain that contains a rigid motion of every planar arc of
length $1$. -/
@[optimization_constant "13a"]
noncomputable def C13a : ℝ≥0∞ :=
  sInf {v | ∃ X ∈ MoserWorm.WormCovers, Convex ℝ X ∧ volume X = v}

/-- The best known lower bound $0.232239$, proven by Khandhawit-Pagonakis-Sriswasdi
in [KPS2013]. -/
@[category research solved, AMS 52]
theorem c13a_lower_bound : 0.232239 ≤ C13a :=
  le_sInf fun _b hb => MoserWorm.convex_mosers_worm_problem_lower_bound hb

/-- An upper bound $0.270911861$, proven by Wang in [Wan2006]. The best known upper bound is
$\pi/12 \approx 0.2617993878$, given by a $30$ degree circular sector of radius $1$
("Wetzel's sector") [PW2021]. -/
@[category research solved, AMS 52]
theorem c13a_upper_bound : C13a ≤ 0.270911861 := by
  sorry

/-- The best known upper bound $\pi/12$, given by Wetzel's sector [PW2021]. -/
@[category research solved, AMS 52]
theorem c13a_upper_bound' : C13a ≤ ENNReal.ofReal (Real.pi / 12) := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ico_c13a : answer(sorry) ∈ Set.Ico C13a (ENNReal.ofReal (Real.pi / 12)) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ioc_c13a : answer(sorry) ∈ Set.Ioc 0.232239 C13a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 52]
theorem c13a_eq : C13a = answer(sorry) := by
  sorry

end Constant13a
