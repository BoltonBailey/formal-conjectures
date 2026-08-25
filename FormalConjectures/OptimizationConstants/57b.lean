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
- [Yan1995] Yanagihara, H. "On the locally univalent Bloch constant." Journal d'Analyse Mathématique
  65 (1995), 1–17. DOI: [10.1007/BF02788763](https://doi.org/10.1007/BF02788763).
- [Rad1943] Rademacher, Hans. "On the Bloch-Landau constant." American Journal of Mathematics 65
  (1943), no. 3, 387–390. DOI: [10.2307/2371963](https://doi.org/10.2307/2371963).

The constant is formalised in `FormalConjectures.Wikipedia.Bloch` as `Bloch.landauConstant`.
-/

namespace Constant57b

/-- **Tao's Optimization constant 57b / Landau's constant**:
the infimum, over all holomorphic $f$ on the unit disc with $f'(0) = 1$, of the radius of the
largest disc contained in $f(\mathbb{D})$. -/
@[optimization_constant "57b"]
noncomputable def C57b : ℝ := Bloch.landauConstant

/-- Lower bound from [Yan1995] (1995). Lower bound attributed to Yanagihara (as summarized in
[BS2023]). [BS2023-bounds-L] -/
@[category research solved, AMS 30]
theorem c57b_lower_bound_yan1995 : 1 / 2 + 10 ^ (-335 : ℤ) ≤ C57b := by
  sorry

/-- Upper bound from [Rad1943] (1943). Upper bound attributed to Rademacher (as summarized in
[BS2023]). [BS2023-bounds-L] -/
@[category research solved, AMS 30]
theorem c57b_upper_bound_rad1943 :
    C57b ≤ (Real.Gamma (1 / 3) * Real.Gamma (5 / 6)) / Real.Gamma (1 / 6) := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 30]
theorem c57b_eq : answer(sorry) = C57b := by
  sorry

end Constant57b
