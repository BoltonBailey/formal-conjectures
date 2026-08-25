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
- [Band2024] Bandeira, A. S. ["Did just a couple of deviations suffice all
  along?"](https://randomstrasse101.math.ethz.ch/posts/HowManyDeviations/) (problems 10–14).
  Randomstrasse 101 blog post (Dec 19, 2024).
- [G2026] Griego, Sebastian. 6 by 6 sign-matrix certificate for C10c, submitted to this repository
  (2026).
- [X2026] Xie, Chuhan. 9 by 9 sign-matrix certificate for C10c, submitted to this repository (2026).

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

/-- Trivial lower bound. $A=[1]$. Also achieved by Hadamard matrices [Band2024]. -/
@[category research solved, AMS 5 11]
theorem c10c_lower_bound_trivial : 1 ≤ C10c := by
  sorry

/-- Lower bound from [Band2024] (2024). The 2 by 2 sign matrix with rows $(1,1)$ and $(1,-1)$. -/
@[category research solved, AMS 5 11]
theorem c10c_lower_bound_band2024 : Real.sqrt 2 ≤ C10c := by
  sorry

/-- Lower bound from [G2026] (2026). A 6 by 6 sign matrix with exact discrepancy $4$. -/
@[category research solved, AMS 5 11]
theorem c10c_lower_bound_g2026 : 4 / Real.sqrt 6 ≤ C10c := by
  sorry

/-- Lower bound from [X2026] (2026). A 9 by 9 sign matrix with exact discrepancy $5$. -/
@[category research solved, AMS 5 11]
theorem c10c_lower_bound_x2026 : 5 / 3 ≤ C10c := by
  sorry

/-- Lower bound from [L2026] (2026). A 17 by 17 sign matrix with exact discrepancy $7$ ($16$
distinct rows, one repeated to square it). -/
@[category research solved, AMS 5 11]
theorem c10c_lower_bound_l2026 : 7 / Real.sqrt 17 ≤ C10c := by
  sorry

/-- Upper bound from [Spe1985] (1985). Usually reported as $6$. The celebrated “six standard
deviations suffice” theorem of Spencer; also applies to rectangular matrices or set systems. -/
@[category research solved, AMS 5 11]
theorem c10c_upper_bound_spe1985 : C10c ≤ 5.32 := by
  sorry

/-- Upper bound from [Bel2013] (2013). Re-optimizes Spencer’s method. -/
@[category research solved, AMS 5 11]
theorem c10c_upper_bound_bel2013_1 : C10c ≤ 5.199 := by
  sorry

/-- Upper bound from Schmidt [Bel2013] (2013). Some of the computations are given only as a personal
communication. -/
@[category research solved, AMS 5 11]
theorem c10c_upper_bound_bel2013_2 : C10c ≤ 3.65 := by
  sorry

/-- Upper bound from [PV2022] (2022). Also gives an algorithmic version. -/
@[category research solved, AMS 5 11]
theorem c10c_upper_bound_pv2022 : C10c ≤ 3 * Real.sqrt (3 / 2) := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c10c_eq : answer(sorry) = C10c := by
  sorry

end Constant10c
