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
import FormalConjectures.Wikipedia.SixStandardDeviations

/-!
# Tao's Optimization constant 10c / The Spencer discrepancy constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 10c](https://teorth.github.io/optimizationproblems/constants/10c.html)
- [Spe1985] Spencer, J. "Six standard deviations suffice." Transactions of the American
  Mathematical Society 289 (1985), 679–706.
- [Bel2013] Bellare, ... Re-optimisation of Spencer's method, 2013.
- [PV2022] Pham, H. T.; Vondrák, J. "Discrepancy minimization via regularization." 2022.
- [L2026] A $17 \times 17$ sign matrix with exact discrepancy $7$, 2026.

Spencer's theorem itself is formalised in
`FormalConjectures.Wikipedia.SixStandardDeviations`.
-/

namespace Constant10c

/-- The **discrepancy** of a square matrix $A$: the minimum of $\|Ax\|_\infty$ over sign
vectors $x \in \{-1, 1\}^n$. -/
noncomputable def disc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x : Fin n → ℝ, (∀ j, x j = 1 ∨ x j = -1) ∧
    r = ⨆ i, |∑ j, A i j * x j|}

/-- **Tao's Optimization constant 10c / The Spencer discrepancy constant**:
the least constant $K$ with $\mathrm{disc}(A) \le K\sqrt{n}$ for every $n$ and every
$A \in [-1, 1]^{n \times n}$. -/
@[optimization_constant "10c"]
noncomputable def C10c : ℝ :=
  sInf {K : ℝ | ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), (∀ i j, |A i j| ≤ 1) →
    disc A ≤ K * Real.sqrt n}

/-- The best known lower bound $7/\sqrt{17}$, given by a $17 \times 17$ sign matrix of exact
discrepancy $7$ [L2026]. -/
@[category research solved, AMS 5 11]
theorem c10c_lower_bound : 7 / Real.sqrt 17 ≤ C10c := by
  sorry

/-- The best known upper bound $3\sqrt{3/2} \approx 3.674235$, proven by Pham-Vondrák
in [PV2022]. Spencer's original "six standard deviations suffice" theorem [Spe1985] gives
$5.32$. -/
@[category research solved, AMS 5 11]
theorem c10c_upper_bound : C10c ≤ 3 * Real.sqrt (3 / 2) := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 5 11]
theorem mem_Ico_c10c : answer(sorry) ∈ Set.Ico C10c (3 * Real.sqrt (3 / 2)) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5 11]
theorem mem_Ioc_c10c : answer(sorry) ∈ Set.Ioc (7 / Real.sqrt 17) C10c := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c10c_eq : C10c = answer(sorry) := by
  sorry

end Constant10c
