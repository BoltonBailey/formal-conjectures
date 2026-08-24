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
# Tao's Optimization constant 57a / Bloch's constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 57a](https://teorth.github.io/optimizationproblems/constants/57a.html)
- [AG1937] Ahlfors, L. V., Grunsky, H. "Über die Blochsche Konstante." Mathematische Zeitschrift 42
  (1937), 671–673.
- [CG1996] Chen, H., Gauthier, P. M. "On Bloch's constant." Journal d'Analyse Mathématique 69
  (1996), 275–291.

The constant is formalised in `FormalConjectures.Wikipedia.Bloch` as `Bloch.blochConstant`.
-/

namespace Constant57a

/-- **Tao's Optimization constant 57a / Bloch's constant**:
the infimum, over all holomorphic $f$ on the unit disc with $f'(0) = 1$, of the radius of the
largest univalent disc contained in $f(\mathbb{D})$. -/
@[optimization_constant "57a"]
noncomputable def C57a : ℝ := Bloch.blochConstant

/-- The best known lower bound $\sqrt{3}/4 + 2 \times 10^{-4}$, proven by Chen-Gauthier
in [CG1996]. -/
@[category research solved, AMS 30]
theorem c57a_lower_bound : Real.sqrt 3 / 4 + 2 * 10 ^ (-4 : ℤ) ≤ C57a :=
  Bloch.blochConstant_lower_bound

/-- The best known upper bound
$\frac{1}{\sqrt{1 + \sqrt{3}}}\frac{\Gamma(1/3) \Gamma(11/12)}{\Gamma(1/4)}$, proven by
Ahlfors-Grunsky in [AG1937]. -/
@[category research solved, AMS 30]
theorem c57a_upper_bound :
    C57a ≤ Real.Gamma (1 / 3) * Real.Gamma (11 / 12) /
      (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3)) :=
  Bloch.blochConstant_upper_bound

/-- How can the upper bound be improved? -/
@[category research open, AMS 30]
theorem mem_Ico_c57a : answer(sorry) ∈ Set.Ico C57a (Real.Gamma (1 / 3) * Real.Gamma (11 / 12) /
    (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3))) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 30]
theorem mem_Ioc_c57a :
    answer(sorry) ∈ Set.Ioc (Real.sqrt 3 / 4 + 2 * 10 ^ (-4 : ℤ)) C57a := by
  sorry

/-- What is the exact value of the constant? Ahlfors and Grunsky conjectured in [AG1937] that
their upper bound is sharp. -/
@[category research open, AMS 30]
theorem c57a_eq : C57a = answer(sorry) := by
  sorry

end Constant57a
