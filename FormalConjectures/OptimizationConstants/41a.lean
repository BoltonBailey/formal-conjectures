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
import FormalConjectures.Wikipedia.MovingSofa

/-!
# Tao's Optimization constant 41a / The moving sofa constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 41a](https://teorth.github.io/optimizationproblems/constants/41a.html)
- [Ha1968] Hammersley, J. M. "On the enfeeblement of mathematical skills by modern mathematics
  and by similar soft intellectual trash in schools and universities." Bull. Inst. Math. Appl. 4
  (1968), 66–85.
- [Ge1992] Gerver, Joseph L. "On moving a sofa around a corner." Geometriae Dedicata 42 (1992),
  267–283.
- [KR2018] Kallus, Yoav; Romik, Dan. "Improved upper bounds in the moving sofa problem."
  Advances in Mathematics 340 (2018), 960–982. [arXiv:1706.06630](https://arxiv.org/abs/1706.06630)
- [Ba2024] Baek, Jineon. "Optimality of Gerver's sofa."
  [arXiv:2411.19826](https://arxiv.org/abs/2411.19826)

The constant is formalised in `FormalConjectures.Wikipedia.MovingSofa` as
`MovingSofa.sofaConstant`.
-/

open scoped ENNReal

namespace Constant41a

/-- **Tao's Optimization constant 41a / The moving sofa constant**:
the largest area of a connected rigid planar shape that can be moved around a right-angled
corner of a hallway of unit width. -/
@[optimization_constant "41a"]
noncomputable def C41a : ℝ≥0∞ := MovingSofa.sofaConstant

/-- The best known lower bound $2.2195$, given by the Gerver sofa [Ge1992]. -/
@[category research solved, AMS 52]
theorem c41a_lower_bound : 2.2195 ≤ C41a := by
  sorry

/-- The best published upper bound $2.37$, proven by Kallus-Romik in [KR2018] with a
computer-assisted argument. -/
@[category research solved, AMS 52]
theorem c41a_upper_bound : C41a ≤ 2.37 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ico_c41a : answer(sorry) ∈ Set.Ico C41a (2.37) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ioc_c41a : answer(sorry) ∈ Set.Ioc (2.2195) C41a := by
  sorry

/-- What is the exact value of the constant? Baek [Ba2024] announced a proof that the Gerver
sofa is optimal, which would give the value `MovingSofa.gerversSofa`. -/
@[category research open, AMS 52]
theorem c41a_eq : C41a = answer(sorry) := by
  sorry

end Constant41a
