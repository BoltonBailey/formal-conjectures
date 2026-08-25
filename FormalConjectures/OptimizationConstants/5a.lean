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
import FormalConjectures.GreensOpenProblems.«31»

/-!
# Tao's Optimization constant 5a / A Sidon set constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 5a](https://teorth.github.io/optimizationproblems/constants/5a.html)
- [ET41] Erdős, P.; Turán, P. "On a problem of Sidon in additive number theory, and on some
  related problems." Journal of the London Mathematical Society 16 (1941), 212–215.
- [Si38] Singer, J. "A theorem in finite projective geometry and some applications to number
  theory." Transactions of the American Mathematical Society 43 (1938), 377–385.
- [CHO25] Carter, H.; Hunter, Z.; O'Bryant, K. "Sidon sets and perturbations."
  [arXiv:2504.11241](https://arxiv.org/abs/2504.11241)
- [Li69] Lindstr\"{o}m, B., An inequality for $B_{2}$-sequences. J. Combinatorial Theory (1969),
  211-212.
- [BFR21] Balogh, J. and F\"{u}redi, Z. and Roy, S., An upper bound on the size of Sidon sets.
  [arXiv:2103.15850](https://arxiv.org/abs/2103.15850) (2021).
- [OBO22] O'Bryant, K., On the size of finite Sidon sets.
  [arXiv:2207.07800](https://arxiv.org/abs/2207.07800) (2022).

A further, currently unpublished, upper bound of $0.97633$ was announced in 2025 by Carter,
Georgiev, Gómez-Serrano, Hunter, O'Bryant, Tao and Wagner using AlphaEvolve.

The counting function is formalised in `FormalConjectures.GreensOpenProblems.«31»` as `Green31.F`.
-/

open Filter

namespace Constant5a

/-- **Tao's Optimization constant 5a / A Sidon set constant**:
the smallest constant $C$ such that every Sidon subset of $\{1, \ldots, N\}$ has at most
$N^{1/2} + (C + o(1))N^{1/4}$ elements. -/
@[optimization_constant "5a"]
noncomputable def C5a : ℝ :=
  sInf {c : ℝ | ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
    Green31.F N ≤ Real.sqrt N + (c + ε) * (N : ℝ) ^ (4⁻¹ : ℝ)}

/-- Lower bound from [Si38] (1938). -/
@[category research solved, AMS 5 11]
theorem c5a_lower_bound_si38 : 0 ≤ C5a := by
  sorry

/-- Upper bound from [ET41], [Li69] (1941, 1969). -/
@[category research solved, AMS 5 11]
theorem c5a_upper_bound_et41_li69 : C5a ≤ 1 := by
  sorry

/-- Upper bound from [BFR21] (2021). -/
@[category research solved, AMS 5 11]
theorem c5a_upper_bound_bfr21 : C5a ≤ 0.998 := by
  sorry

/-- Upper bound from [OBO22] (2022). -/
@[category research solved, AMS 5 11]
theorem c5a_upper_bound_obo22 : C5a ≤ 0.99703 := by
  sorry

/-- Upper bound from [CHO25] (2025). -/
@[category research solved, AMS 5 11]
theorem c5a_upper_bound_cho25 : C5a ≤ 0.98183 := by
  sorry

/-- Upper bound from Carter, Georgiev, Gomez--Serrano, Hunter, O'Bryant, Tao, Wagner
([unpublished](https://terrytao.wordpress.com/2025/11/05/mathematical-exploration-and-discovery-at-scale/#comment-689052),
2025). AlphaEvolve -/
@[category research solved, AMS 5 11]
theorem c5a_upper_bound_carter : C5a ≤ 0.97633 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c5a_eq : answer(sorry) = C5a := by
  sorry

end Constant5a
