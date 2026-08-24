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
# Tao's Optimization constant 34a / The Falconer distance problem threshold in the plane

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 34a](https://teorth.github.io/optimizationproblems/constants/34a.html)
- [Fal1986] Falconer, K. J. "On the Hausdorff dimensions of distance sets." Mathematika 32
  (1985), 206–212.
- [Wol1999] Wolff, T. "Decay of circular means of Fourier transforms of measures."
  International Mathematics Research Notices 1999 (1999), 547–567.
- [GIOW2018] Guth, L.; Iosevich, A.; Ou, Y.; Wang, H. "On Falconer's distance set problem in the
  plane." Inventiones Mathematicae 219 (2020), 779–830.
  [arXiv:1808.09346](https://arxiv.org/abs/1808.09346)
-/

open MeasureTheory Set

namespace Constant34a

/-- The **distance set** of a set in the plane. -/
def distanceSet (E : Set (EuclideanSpace ℝ (Fin 2))) : Set ℝ := {d : ℝ | ∃ x ∈ E, ∃ y ∈ E, d = dist x y}

/-- **Tao's Optimization constant 34a / The Falconer distance problem threshold in the plane**:
the infimum of the $s \in [0, 2]$ such that every compact $E \subseteq \mathbb{R}^2$ with
$\dim_H(E) > s$ has a distance set of positive Lebesgue measure. -/
@[optimization_constant "34a"]
noncomputable def C34a : ℝ :=
  sInf {s : ℝ | s ∈ Icc (0 : ℝ) 2 ∧ ∀ E : Set (EuclideanSpace ℝ (Fin 2)), IsCompact E →
    ENNReal.ofReal s < dimH E → 0 < volume (distanceSet E)}

/-- The best known lower bound $1$, from Falconer's examples [Fal1986]. -/
@[category research solved, AMS 28 42]
theorem c34a_lower_bound : 1 ≤ C34a := by
  sorry

/-- The best known upper bound $5/4$, proven by Guth-Iosevich-Ou-Wang in [GIOW2018].
Falconer [Fal1986] gave $3/2$ and Wolff [Wol1999] gave $4/3$. -/
@[category research solved, AMS 28 42]
theorem c34a_upper_bound : C34a ≤ 5 / 4 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 28 42]
theorem mem_Ico_c34a : answer(sorry) ∈ Set.Ico C34a (5 / 4) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 28 42]
theorem mem_Ioc_c34a : answer(sorry) ∈ Set.Ioc 1 C34a := by
  sorry

/-- What is the exact value of the constant? The **Falconer distance conjecture** in the plane
predicts that it is $1$. -/
@[category research open, AMS 28 42]
theorem c34a_eq : C34a = answer(sorry) := by
  sorry

end Constant34a
