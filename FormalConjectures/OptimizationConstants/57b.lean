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
import FormalConjectures.Wikipedia.Bloch

/-!
# Tao's Optimization constant 57b / Landau's constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 57b](https://teorth.github.io/optimizationproblems/constants/57b.html)
- [Ra1943] Rademacher, H. "On the Bloch-Landau Constant." American Journal of Mathematics 65
  (1943), 387–390.
- [Ya1995] Yanagihara, H. "On the locally univalent Bloch constant." Journal d'Analyse
  Mathématique 65 (1995), 1–17.

The constant is formalised in `FormalConjectures.Wikipedia.Bloch` as `Bloch.landauConstant`.
-/

namespace Constant57b

/-- **Tao's Optimization constant 57b / Landau's constant**:
the infimum, over all holomorphic $f$ on the unit disc with $f'(0) = 1$, of the radius of the
largest disc contained in $f(\mathbb{D})$. -/
@[optimization_constant "57b"]
noncomputable def C57b : ℝ := Bloch.landauConstant

/-- The best known lower bound $1/2 + 10^{-335}$, proven by Yanagihara in [Ya1995]. -/
@[category research solved, AMS 30]
theorem c57b_lower_bound : 0.5 + 10 ^ (-335 : ℤ) ≤ C57b :=
  Bloch.landauConstant_lower_bound

/-- The best known upper bound $\frac{\Gamma(1/3) \Gamma(5/6)}{\Gamma(1/6)}$, proven by
Rademacher in [Ra1943]. -/
@[category research solved, AMS 30]
theorem c57b_upper_bound :
    C57b ≤ Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6) :=
  Bloch.landauConstant_upper_bound

/-- How can the upper bound be improved? -/
@[category research open, AMS 30]
theorem mem_Ico_c57b :
    answer(sorry) ∈
      Set.Ico C57b (Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6)) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 30]
theorem mem_Ioc_c57b : answer(sorry) ∈ Set.Ioc (0.5 + 10 ^ (-335 : ℤ)) C57b := by
  sorry

/-- What is the exact value of the constant? Rademacher believed that his upper bound is
sharp. -/
@[category research open, AMS 30]
theorem c57b_eq : C57b = answer(sorry) := by
  sorry

end Constant57b
