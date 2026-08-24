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
import FormalConjectures.Wikipedia.ElliottHalberstamConjecture

/-!
# Tao's Optimization constant 66a / The Elliott-Halberstam level-of-distribution exponent

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 66a](https://teorth.github.io/optimizationproblems/constants/66a.html)
- [EH1970] Elliott, P. D. T. A.; Halberstam, H. "A conjecture in prime number theory." Symposia
  Mathematica, Vol. IV (1968/69), 59–72.
- [Ked2007] Kedlaya, K. Notes on the Bombieri-Vinogradov theorem, 2007.

The error term $E(x, q)$ is formalised in
`FormalConjectures.Wikipedia.ElliottHalberstamConjecture` as
`ElliottHalberstamConjecture.E`.
-/

open Filter

namespace Constant66a

/-- **Tao's Optimization constant 66a / The Elliott-Halberstam level-of-distribution exponent**:
the supremum of the admissible levels of distribution $\vartheta$ for the primes, i.e. of those
$\vartheta$ for which $\sum_{q \le x^\vartheta} E(x, q) \ll_A x (\log x)^{-A}$ for every
$A > 0$. -/
@[optimization_constant "66a"]
noncomputable def C66a : ℝ :=
  sSup {θ : ℝ | ∀ A > (0 : ℝ), ∃ C > (0 : ℝ), ∀ x : ℕ, 2 < x →
    ∑ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ θ⌋₊, ElliottHalberstamConjecture.E x q ≤
      C * x / Real.log x ^ A}

/-- The best known lower bound $1/2$, coming from the Bombieri-Vinogradov theorem
[Ked2007]. -/
@[category research solved, AMS 11]
theorem c66a_lower_bound : 1 / 2 ≤ C66a := by
  sorry

/-- The trivial upper bound $1$. -/
@[category research solved, AMS 11]
theorem c66a_upper_bound : C66a ≤ 1 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ioc_c66a : answer(sorry) ∈ Set.Ioc (1 / 2) C66a := by
  sorry

/-- What is the exact value of the constant? The **Elliott-Halberstam conjecture** [EH1970]
asserts that it is $1$. -/
@[category research open, AMS 11]
theorem c66a_eq : C66a = answer(sorry) := by
  sorry

end Constant66a
