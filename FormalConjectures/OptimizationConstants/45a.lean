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
import FormalConjectures.ErdosProblems.«16»

/-!
# Tao's Optimization constant 45a / Romanoff's constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 45a](https://teorth.github.io/optimizationproblems/constants/45a.html)
- [R1934] Romanoff, N. P. "Über einige Sätze der additiven Zahlentheorie." Mathematische Annalen
  109 (1934), 668–678.
- [E1950] Erdős, P. "On integers of the form $2^k + p$ and some related problems." Summa Brasil.
  Math. 2 (1950), 113–123.
- [CE2018] Chen, Y.-G.; Elsholtz, C. "Lower bounds for Romanoff's constant." 2018.
- [Y2026] Upper bound $0.490180063290061$, 2026.

The complementary set is formalised in `FormalConjectures.ErdosProblems.«16»` as
`Erdos16.Erdos16Set`.
-/

open Filter Nat

namespace Constant45a

open scoped Classical in
/-- **Tao's Optimization constant 45a / Romanoff's constant**:
the asymptotic density of the set of odd integers of the form $p + 2^k$ with $p$ prime and
$k \ge 0$. The density is not known to exist, so we take a `limsup`. -/
@[optimization_constant "45a"]
noncomputable def C45a : ℝ :=
  limsup (fun N : ℕ =>
    (count (fun n => Odd n ∧ ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p) N : ℝ) / N) atTop

/-- The best known lower bound $0.107648$, proven by Chen-Elsholtz in [CE2018]. Romanoff [R1934]
first proved that the density is positive. -/
@[category research solved, AMS 11]
theorem c45a_lower_bound : 0.107648 ≤ C45a := by
  sorry

/-- The best known upper bound $0.490180063290061$ [Y2026]. Erdős [E1950] first proved, using
covering systems, that the density is strictly less than the trivial bound $1/2$. -/
@[category research solved, AMS 11]
theorem c45a_upper_bound : C45a ≤ 0.490180063290061 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ico_c45a : answer(sorry) ∈ Set.Ico C45a 0.490180063290061 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ioc_c45a : answer(sorry) ∈ Set.Ioc 0.107648 C45a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c45a_eq : C45a = answer(sorry) := by
  sorry

end Constant45a
