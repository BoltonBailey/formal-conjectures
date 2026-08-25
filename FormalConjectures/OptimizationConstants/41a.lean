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
- [Hammersley1968] Dr. J. M. Hammersley (1968). On the enfeeblement of mathematical skills by modern
  mathematics and by similar soft intellectual trash in schools and universities. Bulletin of the
  Institute of Mathematics and Its Applications. 4: 66–85. See Appendix IV, Problems, Problem 8, p.
  84.
- [Gerver1992] Gerver, Joseph L. (1992). On Moving a Sofa Around a Corner. Geometriae Dedicata. 42
  (3): 267–283.
- [Baek2024] Baek, J. (2024). Optimality of Gerver's Sofa. arXiv preprint arXiv:2411.19826.

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

/-- Lower bound from [Hammersley1968] (1968). -/
@[category research solved, AMS 52]
theorem c41a_lower_bound_hammersley1968 : ENNReal.ofReal (Real.pi / 2 + 2 / Real.pi) ≤ C41a := by
  sorry

/-- Lower bound from [Gerver1992] (1992). The Gerver sofa -/
@[category research solved, AMS 52]
theorem c41a_lower_bound_gerver1992 : 2.2195 ≤ C41a := by
  sorry

/-- Upper bound from [Hammersley1968] (1968). -/
@[category research solved, AMS 52]
theorem c41a_upper_bound_hammersley1968 : C41a ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  sorry

/-- Upper bound from [KR2018] (2018). Best published bound, using a computer-assisted proof scheme
-/
@[category research solved, AMS 52]
theorem c41a_upper_bound_kr2018 : C41a ≤ 2.37 := by
  sorry

/-- Upper bound from [Baek2024] (2024). Announced bound, matching the Gerver construction -/
@[category research solved, AMS 52]
theorem c41a_upper_bound_baek2024 : C41a ≤ 2.2195 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 52]
theorem c41a_eq : answer(sorry) = C41a := by
  sorry

end Constant41a
