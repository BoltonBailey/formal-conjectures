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
# Tao's Optimization constant 87a / Martinet's constant for totally real number fields

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 87a](https://teorth.github.io/optimizationproblems/constants/87a.html)
- [GS1964] Golod, E. S.; Shafarevich, I. R. "On the class field tower." Izv. Akad. Nauk SSSR Ser.
  Mat. 28 (1964), 261–272.
- [Mar1978] Martinet, J. "Tours de corps de classes et estimations de discriminants."
  Inventiones Mathematicae 44 (1978), 65–73.
- [Odl1990] Odlyzko, A. M. "Bounds for discriminants and related estimates for class numbers,
  regulators and zeros of zeta functions: a survey of recent results." Séminaire de Théorie des
  Nombres de Bordeaux 2 (1990), 119–141.
- [HMR2019] Hajir, F.; Maire, C.; Ramakrishna, R. "Cutting towers of number fields." 2019.
-/

open NumberField

namespace Constant87a

/-- The **root discriminant** $\mathrm{rd}(K) = |\Delta_K|^{1/[K : \mathbb{Q}]}$ of a number
field. -/
noncomputable def rootDiscriminant (K : Type) [Field K] [NumberField K] : ℝ :=
  |(discr K : ℝ)| ^ ((Module.finrank ℚ K : ℝ)⁻¹)

/-- **Tao's Optimization constant 87a / Martinet's constant for totally real number fields**:
the smallest $\alpha$ such that there are totally real number fields of arbitrarily large degree
with root discriminant at most $\alpha + \varepsilon$, for every $\varepsilon > 0$. -/
@[optimization_constant "87a"]
noncomputable def C87a : ℝ :=
  sInf {α : ℝ | ∀ ε > (0 : ℝ), ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K),
    IsTotallyReal K ∧ N ≤ Module.finrank ℚ K ∧ rootDiscriminant K ≤ α + ε}

/-- The best known lower bound $60.8395\ldots$, Odlyzko's unconditional bound on the root
discriminant of a totally real number field of large degree [Odl1990]. Under the generalised
Riemann hypothesis the Odlyzko-Serre bound is $215.333\ldots$. -/
@[category research solved, AMS 11]
theorem c87a_lower_bound : 60.8395 ≤ C87a := by
  sorry

/-- The best known upper bound $857.567$, proven by Hajir-Maire-Ramakrishna in [HMR2019] by
"cutting towers". Martinet's original construction [Mar1978], via the Golod-Shafarevich
criterion [GS1964], gives $1058.565$. -/
@[category research solved, AMS 11]
theorem c87a_upper_bound : C87a ≤ 857.567 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ico_c87a : answer(sorry) ∈ Set.Ico C87a 857.567 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ioc_c87a : answer(sorry) ∈ Set.Ioc 60.8395 C87a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c87a_eq : C87a = answer(sorry) := by
  sorry

end Constant87a
