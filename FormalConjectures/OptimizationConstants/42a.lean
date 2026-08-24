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
import FormalConjectures.ErdosProblems.«519»

/-!
# Tao's Optimization constant 42a / Turán's pure power sum constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 42a](https://teorth.github.io/optimizationproblems/constants/42a.html)
- [Atk61] Atkinson, F. V. "On sums of powers of complex numbers." Acta Math. Acad. Sci. Hungar. 12
  (1961), 185–188.
- [Bir94] Biró, A. "On a problem of Turán concerning sums of powers of complex numbers." Acta
  Math. Hungar. 65 (1994), 209–216.
- [Bir00] Biró, A. "An upper estimate in Turán's pure power sum problem." Acta Math. Hungar. 86
  (2000), 231–238.

The power sums are formalised in `FormalConjectures.ErdosProblems.«519»` as `Erdos519.powerSum`.
-/

open Filter

namespace Constant42a

/-- The quantity $R_n$: the minimum over $z_1, \ldots, z_n \in \mathbb{C}$ with
$\max_i |z_i| = 1$ of $\max_{1 \le k \le n} \left| \sum_i z_i^k \right|$. -/
noncomputable def R (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ z : Fin n → ℂ, (⨆ i, ‖z i‖) = 1 ∧
    r = ⨆ k : Fin n, ‖Erdos519.powerSum z (k.val + 1)‖}

/-- **Tao's Optimization constant 42a / Turán's pure power sum constant**:
$\limsup_{n \to \infty} R_n$, where $R_n$ is the minimum over unit-normalised
$z_1, \ldots, z_n \in \mathbb{C}$ of $\max_{1 \le k \le n} \left| \sum_i z_i^k \right|$. -/
@[optimization_constant "42a"]
noncomputable def C42a : ℝ := limsup R atTop

/-- The best known lower bound $1/2$, proven by Biró in [Bir94]. Biró later showed in [Bir00]
that the constant is strictly larger than $1/2$, without computing an explicit value. -/
@[category research solved, AMS 11 30]
theorem c42a_lower_bound : 1 / 2 ≤ C42a := by
  sorry

/-- The best known upper bound $0.69368$, due to Harcos and reported in [Bir00]. -/
@[category research solved, AMS 11 30]
theorem c42a_upper_bound : C42a ≤ 0.69368 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11 30]
theorem mem_Ico_c42a : answer(sorry) ∈ Set.Ico C42a 0.69368 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11 30]
theorem mem_Ioc_c42a : answer(sorry) ∈ Set.Ioc (1 / 2) C42a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11 30]
theorem c42a_eq : C42a = answer(sorry) := by
  sorry

end Constant42a
