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
# Tao's Optimization constant 58a / Zaremba's conjecture constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 58a](https://teorth.github.io/optimizationproblems/constants/58a.html)
- [Zar1972] Zaremba, S. K. "La méthode des bons treillis pour le calcul des intégrales
  multiples." Applications of Number Theory to Numerical Analysis (1972), 39–119.
- [BK2014] Bourgain, J.; Kontorovich, A. "On Zaremba's conjecture." Annals of Mathematics 180
  (2014), 137–196.
- [Hua2015] Huang, S. "An improvement to Zaremba's conjecture." Geometric and Functional
  Analysis 25 (2015), 860–914.
- [Kan2021] Kan, I. D. Survey of Zaremba's conjecture, 2021.
-/

open scoped ENNReal

namespace Constant58a

/-- All partial quotients of the continued fraction expansion of a rational number are at most
`A`. -/
def PartialQuotientsLE (q : ℚ) (A : ℕ) : Prop :=
  ∀ (n : ℕ) (b : ℚ), (GenContFract.of q).partDens.get? n = some b → b ≤ (A : ℚ)

/-- **Tao's Optimization constant 58a / Zaremba's conjecture constant**:
the least integer $A$ such that every positive integer $d$ is the denominator of some reduced
fraction $b/d \in (0, 1)$ whose finite continued fraction has all partial quotients at most $A$,
or $\infty$ if no such $A$ exists. -/
@[optimization_constant "58a"]
noncomputable def C58a : ℕ∞ :=
  sInf {A : ℕ∞ | ∃ m : ℕ, A = m ∧ ∀ d : ℕ, 0 < d →
    ∃ b : ℕ, 0 < b ∧ b < d ∧ Nat.Coprime b d ∧ PartialQuotientsLE ((b : ℚ) / d) m}

/-- Lower bound from [Kan2021] (2021). The $A=4$ version fails (counterexamples $d=54,150$), so any
universal bound must satisfy $A_{\mathrm{Zar}}\ge 5$. [Kan2021-A4-counterexamples] -/
@[category research solved, AMS 11]
theorem c58a_lower_bound_kan2021 : 5 ≤ C58a := by
  sorry

/-- Trivial upper bound. Trivial. -/
@[category research solved, AMS 11]
theorem c58a_upper_bound_trivial : C58a ≤ ⊤ := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c58a_eq : answer(sorry) = C58a := by
  sorry

end Constant58a
