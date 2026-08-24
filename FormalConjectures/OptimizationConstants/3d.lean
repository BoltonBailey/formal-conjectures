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
# Tao's Optimization constant 3d / The single-set sum-difference exponent

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 3d](https://teorth.github.io/optimizationproblems/constants/3d.html)
- [Ru96] Ruzsa, I. Z. "Sums of finite sets." Number Theory (New York, 1991–1995), Springer
  (1996), 281–293.
- [PeWe13] Penman, D.; Wells, M. "On sets with more restricted sums than differences."
  Integers 13 (2013), A57.
- [LiLi26] Solution of the problem, establishing that the exponent equals $2$, 2026.
-/

open scoped Pointwise Finset

namespace Constant3d

/-- The doubling constant $\sigma(A) = |A + A| / |A|$ of a finite set. -/
noncomputable def σ (A : Finset ℤ) : ℝ := (#(A + A) : ℝ) / #A

/-- The difference constant $\delta(A) = |A - A| / |A|$ of a finite set. -/
noncomputable def δ (A : Finset ℤ) : ℝ := (#(A - A) : ℝ) / #A

/-- **Tao's Optimization constant 3d / The single-set sum-difference exponent**:
the supremum of $\log \sigma(A) / \log \delta(A)$ over finite sets $A$ of integers with
$|A| \ge 2$ and $\delta(A) > 1$; equivalently the least $\theta$ with
$\sigma(A) \le \delta(A)^\theta$ for every finite $A$. -/
@[optimization_constant "3d"]
noncomputable def C3d : ℝ :=
  sSup {t : ℝ | ∃ A : Finset ℤ, 2 ≤ #A ∧ 1 < δ A ∧ t = Real.log (σ A) / Real.log (δ A)}

/-- The lower bound $2$, proven in [LiLi26], which solves the problem. The previous record
$\log(32/5) / \log(26/5) = 1.125944\ldots$ was due to Penman-Wells [PeWe13]. -/
@[category research solved, AMS 5 11]
theorem c3d_lower_bound : 2 ≤ C3d := by
  sorry

/-- The upper bound $2$, which is Ruzsa's inequality $\sigma \le \delta^2$ [Ru96], a consequence
of the Plünnecke-Ruzsa inequalities. -/
@[category research solved, AMS 5 11]
theorem c3d_upper_bound : C3d ≤ 2 := by
  sorry

/-- The exact value of the constant is $2$, established in [LiLi26]. The value is approached but
not attained by the known constructions. -/
@[category research solved, AMS 5 11]
theorem c3d_eq : C3d = 2 :=
  le_antisymm c3d_upper_bound c3d_lower_bound

end Constant3d
