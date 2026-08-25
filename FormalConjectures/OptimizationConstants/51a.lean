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
- [S2026] Sothanaphan, Nat. "A certified computation for an improved He–Tang parameter choice in
  Erdős’ maximum-term problem." 2026.
  https://drive.google.com/file/d/1wZnzui_eeBE32HnkrnSB7YhfcTOiYolp/view

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

/-- Lower bound from [Er1961] (1961). -/
@[category research solved, AMS 30]
theorem c51a_lower_bound_er1961 : 1 / 2 ≤ C51a := by
  sorry

/-- Lower bound from Kövári (unpublished). Cited in [HT2026] -/
@[category research solved, AMS 30]
theorem c51a_lower_bound_kovari : 1 / 2 < C51a := by
  sorry

/-- Lower bound from [CH1964] (1964). Scaling-identity construction. -/
@[category research solved, AMS 30]
theorem c51a_lower_bound_ch1964 : 4 / 7 ≤ C51a := by
  sorry

/-- Lower bound from [HT2026] (2026). Certified (computer-assisted) improvement using a
two-parameter generalization of the Clunie–Hayman construction. -/
@[category research solved, AMS 30]
theorem c51a_lower_bound_ht2026 : 0.5850724 ≤ C51a := by
  sorry

/-- Lower bound from [S2026] (2026). Used GPT 5.2. Discussed
[here](https://www.erdosproblems.com/forum/thread/513#post-4532) -/
@[category research solved, AMS 30]
theorem c51a_lower_bound_s2026 : 0.5850788 ≤ C51a := by
  sorry

/-- Trivial upper bound. Follows from Cauchy estimates -/
@[category research solved, AMS 30]
theorem c51a_upper_bound_trivial : C51a ≤ 1 := by
  sorry

/-- Upper bound from [CH1964] (1964). -/
@[category research solved, AMS 30]
theorem c51a_upper_bound_ch1964 : C51a ≤ 2 / Real.pi := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 30]
theorem c51a_eq : answer(sorry) = C51a := by
  sorry

end Constant51a
