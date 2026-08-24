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

The constant is formalised in `FormalConjectures.Wikipedia.Bloch` as
`Bloch.univalentBlochConstant`.
-/

namespace Constant57c

/-- **Tao's Optimization constant 57c / The univalent Bloch constant**:
the infimum, over all univalent holomorphic $f$ on the unit disc with $f'(0) = 1$, of the radius
of the largest univalent disc contained in $f(\mathbb{D})$. -/
@[optimization_constant "57c"]
noncomputable def C57c : ℝ := Bloch.univalentBlochConstant

/-- The best known lower bound $0.5708858$, proven by Skinner in [Skin2009]. -/
@[category research solved, AMS 30]
theorem c57c_lower_bound : 0.5708858 ≤ C57c :=
  Bloch.univalentBlochConstant_lower_bound

/-- The best known upper bound is the trivial bound $1$, coming from the identity function. -/
@[category research solved, AMS 30]
theorem c57c_upper_bound : C57c ≤ 1 :=
  Bloch.univalentBlochConstant_upper_bound

/-- How can the upper bound be improved? -/
@[category research open, AMS 30]
theorem mem_Ico_c57c : answer(sorry) ∈ Set.Ico C57c 1 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 30]
theorem mem_Ioc_c57c : answer(sorry) ∈ Set.Ioc 0.5708858 C57c := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 30]
theorem c57c_eq : C57c = answer(sorry) := by
  sorry

end Constant57c
