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
import FormalConjectures.ErdosProblems.«513»

/-!
# Tao's Optimization constant 51a / The Erdős maximum-term constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 51a](https://teorth.github.io/optimizationproblems/constants/51a.html)
- [Er1961] Erdős, P. "Some unsolved problems." Magyar Tud. Akad. Mat. Kutató Int. Közl. 6 (1961),
  221–254.
- [CH1964] Clunie, J.; Hayman, W. K. "The maximum term of a power series." Journal d'Analyse
  Mathématique 12 (1964), 143–186.
- [HT2026] Hunter, Z.; Tao, T. "Improved bounds for the maximum term problem." 2026.

The underlying ratio is formalised in `FormalConjectures.ErdosProblems.«513»` as `Erdos513.ratio`.
-/

open Filter Polynomial
open scoped Real

namespace Constant51a

/-- **Tao's Optimization constant 51a / The Erdős maximum-term constant**:
the supremum over transcendental entire functions $f$ of
$\liminf_{r \to \infty} \frac{\mu(r, f)}{M(r, f)}$, where $\mu(r, f)$ is the maximum term of the
power series of $f$ and $M(r, f)$ is the maximum modulus of $f$ on the circle of radius $r$. -/
@[optimization_constant "51a"]
noncomputable def C51a : ℝ :=
  ⨆ f : {f : ℂ → ℂ // Transcendental ℂ[X] f ∧ Differentiable ℂ f},
    liminf (fun r : ℝ => Erdos513.ratio r f) atTop

/-- The best known lower bound $0.5850724$, a certified computer-assisted improvement of the
Clunie-Hayman construction due to Hunter-Tao [HT2026]. -/
@[category research solved, AMS 30]
theorem c51a_lower_bound : 0.5850724 ≤ C51a := by
  sorry

/-- The best known upper bound $2/\pi$, proven by Clunie-Hayman in [CH1964]. -/
@[category research solved, AMS 30]
theorem c51a_upper_bound : C51a ≤ 2 / π := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 30]
theorem mem_Ico_c51a : answer(sorry) ∈ Set.Ico C51a (2 / π) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 30]
theorem mem_Ioc_c51a : answer(sorry) ∈ Set.Ioc 0.5850724 C51a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 30]
theorem c51a_eq : C51a = answer(sorry) := by
  sorry

end Constant51a
