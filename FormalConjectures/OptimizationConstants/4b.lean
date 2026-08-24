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
# Tao's Optimization constant 4b / The Furstenberg-Sárközy exponent

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 4b](https://teorth.github.io/optimizationproblems/constants/4b.html)
- [Sar1978] Sárközy, A. "On difference sets of sequences of integers I." Acta Mathematica
  Academiae Scientiarum Hungaricae 31 (1978), 125–149.
- [Ruz1984] Ruzsa, I. Z. "Difference sets without squares." Periodica Mathematica Hungarica 15
  (1984), 205–209.
- [Lew2015] Lewko, M. "An improved lower bound related to the Furstenberg-Sárközy theorem."
  Electronic Journal of Combinatorics 22 (2015), P1.32.
-/

open Filter
open scoped Finset

namespace Constant4b

/-- The largest size of a subset of $\{1, \ldots, N\}$ with no non-zero square difference. -/
noncomputable def squareDifferenceFreeCard (N : ℕ) : ℕ :=
  sSup {#A | (A : Finset ℕ) (_ : A ⊆ Finset.Icc 1 N)
    (_ : ∀ a ∈ A, ∀ b ∈ A, ∀ n : ℕ, n ≠ 0 → a ≠ b + n ^ 2)}

/-- **Tao's Optimization constant 4b / The Furstenberg-Sárközy exponent**:
the least constant $c$ with $r(N) \le N^{c + o(1)}$, where $r(N)$ is the largest size of a
square-difference-free subset of $\{1, \ldots, N\}$. We take a `limsup`, since the existence of
the limit is itself open [Ruz1984]. -/
@[optimization_constant "4b"]
noncomputable def C4b : ℝ :=
  limsup (fun N : ℕ => Real.log (squareDifferenceFreeCard N) / Real.log N) atTop

/-- The best known lower bound $\frac12(1 + \log 12 / \log 205) \approx 0.733412$, proven by
Lewko in [Lew2015], refining Ruzsa's base-expansion construction [Ruz1984]. -/
@[category research solved, AMS 5 11]
theorem c4b_lower_bound :
    (1 / 2) * (1 + Real.log 12 / Real.log 205) ≤ C4b := by
  sorry

/-- The trivial upper bound $1$. The known quantitative forms of the Furstenberg-Sárközy
theorem [Sar1978] do not yet improve on it. -/
@[category research solved, AMS 5 11]
theorem c4b_upper_bound : C4b ≤ 1 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 5 11]
theorem mem_Ico_c4b : answer(sorry) ∈ Set.Ico C4b 1 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5 11]
theorem mem_Ioc_c4b :
    answer(sorry) ∈ Set.Ioc ((1 / 2) * (1 + Real.log 12 / Real.log 205)) C4b := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c4b_eq : C4b = answer(sorry) := by
  sorry

end Constant4b
