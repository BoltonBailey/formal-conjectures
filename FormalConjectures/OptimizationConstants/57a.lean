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

/-- Lower bound from [CG1996] (1996). Best recorded lower bound (as quoted in the survey
literature). [BS2023-bounds-B] -/
@[category research solved, AMS 30]
theorem c57a_lower_bound_cg1996 : Real.sqrt 3 / 4 + 2 * 10 ^ (-4 : ℤ) ≤ C57a := by
  sorry

/-- Upper bound from [AG1937] (1937). Ahlfors–Grunsky bound; conjectured sharp. [BS2023-AG-conj-B]
[BS2023-bounds-B] -/
@[category research solved, AMS 30]
theorem c57a_upper_bound_ag1937 :
    C57a ≤ 1 / Real.sqrt (1 + Real.sqrt 3) *
      ((Real.Gamma (1 / 3) * Real.Gamma (11 / 12)) / Real.Gamma (1 / 4)) := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 30]
theorem c57a_eq : answer(sorry) = C57a := by
  sorry

end Constant57a
