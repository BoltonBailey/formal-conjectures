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
# Tao's Optimization constant 57c / The univalent Bloch constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 57c](https://teorth.github.io/optimizationproblems/constants/57c.html)
- [Skin2009] Skinner, Brian. "The univalent Bloch constant problem." Complex Variables and
  Elliptic Equations 54 (2009), no. 10, 951–955.
- [Yan1995] Yanagihara, H. "On the locally univalent Bloch constant." Journal d'Analyse Mathématique
  65 (1995), 1–17. DOI: [10.1007/BF02788763](https://doi.org/10.1007/BF02788763).

The constant is formalised in `FormalConjectures.Wikipedia.Bloch` as
`Bloch.univalentBlochConstant`.
-/

namespace Constant57c

/-- **Tao's Optimization constant 57c / The univalent Bloch constant**:
the infimum, over all univalent holomorphic $f$ on the unit disc with $f'(0) = 1$, of the radius
of the largest univalent disc contained in $f(\mathbb{D})$. -/
@[optimization_constant "57c"]
noncomputable def C57c : ℝ := Bloch.univalentBlochConstant

/-- Lower bound from [Yan1995] (1995). Follows from $L\le B_u$ together with Yanagihara's lower
bound for $L$ as summarized in [BS2023]. [BS2023-relations] [BS2023-bounds-L] -/
@[category research solved, AMS 30]
theorem c57c_lower_bound_yan1995 : 1 / 2 + 10 ^ (-335 : ℤ) ≤ C57c := by
  sorry

/-- Lower bound from [Skin2009] (2009). Best recorded lower bound (as summarized in [BS2023]).
[BS2023-latest-Bu-lb] -/
@[category research solved, AMS 30]
theorem c57c_lower_bound_skin2009 : 0.5708858 ≤ C57c := by
  sorry

/-- Trivial upper bound. The identity function $f(z)=z$ is univalent with $f'(0)=1$ and has $B_f=1$,
hence $B_u\le 1$. -/
@[category research solved, AMS 30]
theorem c57c_upper_bound_trivial : C57c ≤ 1 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 30]
theorem c57c_eq : answer(sorry) = C57c := by
  sorry

end Constant57c
