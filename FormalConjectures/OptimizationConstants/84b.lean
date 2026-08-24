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
# Tao's Optimization constant 84b / The sum-product exponent for the reals

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 84b](https://teorth.github.io/optimizationproblems/constants/84b.html)
- [ErSz83] Erdős, P.; Szemerédi, E. "On sums and products of integers." Studies in Pure
  Mathematics, Birkhäuser (1983), 213–218.
- [So09] Solymosi, J. "Bounding multiplicative energy by the sumset." Advances in Mathematics 222
  (2009), 402–408.
- [Cu25] Cushman, A. Current record lower bound, 2025.
- [BSSZ2026] Bloom, T. F.; Sawin, W.; Schildkraut, K.; Zhelezov, D. Disproof of the sum-product
  conjecture for the reals, 2026.
-/

open Filter
open scoped Pointwise Finset

namespace Constant84b

/-- **Tao's Optimization constant 84b / The sum-product exponent for the reals**:
$\liminf_n \min_{|A| = n} \frac{\log \max(|A + A|, |AA|)}{\log n}$ over finite sets
$A \subseteq \mathbb{R}$. -/
@[optimization_constant "84b"]
noncomputable def C84b : ℝ :=
  liminf (fun n : ℕ => sInf {t : ℝ | ∃ A : Finset ℝ, #A = n ∧
    t = Real.log (max (#(A + A) : ℝ) (#(A * A) : ℝ)) / Real.log n}) atTop

/-- The best known lower bound $4/3 + 10/4407 \approx 1.335602$, proven by Cushman in [Cu25],
refining Solymosi's $4/3$ barrier [So09]. -/
@[category research solved, AMS 5 11]
theorem c84b_lower_bound : 4 / 3 + 10 / 4407 ≤ C84b := by
  sorry

/-- The upper bound $2$, from the Erdős-Szemerédi construction [ErSz83], which was conjectured
to be sharp. -/
@[category research solved, AMS 5 11]
theorem c84b_upper_bound : C84b ≤ 2 := by
  sorry

/-- The **sum-product conjecture for the reals** was disproved by
Bloom-Sawin-Schildkraut-Zhelezov in [BSSZ2026]: the exponent is strictly less than $2$. -/
@[category research solved, AMS 5 11]
theorem c84b_lt_two : C84b < 2 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 5 11]
theorem mem_Ico_c84b : answer(sorry) ∈ Set.Ico C84b 2 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5 11]
theorem mem_Ioc_c84b : answer(sorry) ∈ Set.Ioc (4 / 3 + 10 / 4407) C84b := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c84b_eq : C84b = answer(sorry) := by
  sorry

end Constant84b
