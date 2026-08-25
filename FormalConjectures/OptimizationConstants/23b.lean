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
# Tao's Optimization constant 23b / The condition-number decay exponent for sign matrices

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 23b](https://teorth.github.io/optimizationproblems/constants/23b.html)
- [AJM2025] Alon, N.; ... ; Problem 11 on the condition number of sign matrices, 2025.

The constant $\kappa(n)$ equals $1$ exactly when a Hadamard matrix of order $n$ exists; see
`FormalConjectures.OptimizationConstants.«23a»`.
-/

open Filter
open scoped ENNReal

namespace Constant23b

variable {n : ℕ}

/-- The Euclidean norm of a vector, written out so that the definition stays elementary. -/
noncomputable def nrm (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- The largest singular value $\sigma_{\max}(A) = \sup_{\|x\| = 1} \|Ax\|$. -/
noncomputable def sMax (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : Fin n → ℝ, nrm x = 1 ∧ r = nrm (A.mulVec x)}

/-- The smallest singular value $\sigma_{\min}(A) = \inf_{\|x\| = 1} \|Ax\|$. -/
noncomputable def sMin (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x : Fin n → ℝ, nrm x = 1 ∧ r = nrm (A.mulVec x)}

/-- The **condition number** $\kappa(A) = \sigma_{\max}(A) / \sigma_{\min}(A)$, taken in
`ℝ≥0∞` so that a singular matrix correctly gets the value $\infty$. -/
noncomputable def cond (A : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (sMax A) / ENNReal.ofReal (sMin A)

/-- $\kappa(n)$, the least condition number of an $n \times n$ sign matrix. -/
noncomputable def kappa (n : ℕ) : ℝ≥0∞ :=
  ⨅ A : {A : Matrix (Fin n) (Fin n) ℝ // ∀ i j, A i j = 1 ∨ A i j = -1}, cond A.1

/-- **Tao's Optimization constant 23b / The condition-number decay exponent for sign
matrices**: the largest $\alpha$ for which $\kappa(n) = 1 + f(n)/n^\alpha$ for some
subpolynomial $f$. -/
@[optimization_constant "23b"]
noncomputable def C23b : ℝ :=
  sSup {α : ℝ | 0 ≤ α ∧ ∃ f : ℕ → ℝ,
    (∀ ε > (0 : ℝ), f =O[atTop] fun n : ℕ => (n : ℝ) ^ ε) ∧
    ∀ᶠ n : ℕ in atTop, kappa n = ENNReal.ofReal (1 + f n / (n : ℝ) ^ α)}

/-- Trivial lower bound. Take $\alpha=0$ and $f(n)=\kappa(n)-1$. Since $\kappa(n)\to 1$ as
$n\to\infty$, $f$ is bounded (hence subpolynomial). [AJM2025-abstract-kappa-to-1] -/
@[category research solved, AMS 5 15]
theorem c23b_lower_bound_trivial : 0 ≤ C23b := by
  sorry

/-- Lower bound from [AJM2025] (2025). The authors state that (unconditionally) their method permits
$\kappa(n)\le 1+\frac{1}{n^\alpha}$ for all sufficiently large $n$ with $\alpha=17/92-\delta$ for
any small $\delta>0$. [AJM2025-thm1-alpha] -/
@[category research solved, AMS 5 15]
theorem c23b_lower_bound_ajm2025 : 17 / 92 ≤ C23b := by
  sorry

/-- Upper bound from [AJM2025] (2025). Stated in the discussion of Problem 11. [AJM2025-prob11] (A
supporting mechanism is the lower bound $\kappa(n)\ge 1+c\frac{\log n}{n}$ for $n\not\equiv 0 \pmod
4$.) [AJM2025-thm6] -/
@[category research solved, AMS 5 15]
theorem c23b_upper_bound_ajm2025 : C23b ≤ 1 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 15]
theorem c23b_eq : answer(sorry) = C23b := by
  sorry

end Constant23b
