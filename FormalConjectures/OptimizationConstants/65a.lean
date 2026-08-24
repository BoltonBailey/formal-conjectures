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
# Tao's Optimization constant 65a / Linnik's constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 65a](https://teorth.github.io/optimizationproblems/constants/65a.html)
- [Lin1944] Linnik, Yu. V. "On the least prime in an arithmetic progression." Rec. Math.
  (Mat. Sbornik) 15 (1944), 139–178 and 347–368.
- [Xyl2011] Xylouris, T. "On the least prime in an arithmetic progression and estimates for the
  zeros of Dirichlet L-functions." Acta Arithmetica 150 (2011), 65–91.
- [MMT2024] Maynard, J.; Merikoski, J.; Thorner, J. An $L$-function-free proof of Linnik's
  theorem, 2024.
-/

namespace Constant65a

/-- The least prime in the arithmetic progression $a \bmod q$. -/
noncomputable def leastPrime (a q : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ (p : ZMod q) = (a : ZMod q)}

/-- **Tao's Optimization constant 65a / Linnik's constant**:
the infimum of the exponents $L$ for which $P(a, q) \le C q^L$ holds for all $q \ge 2$ and all
$a$ coprime to $q$, with a constant $C$ independent of $a$ and $q$. -/
@[optimization_constant "65a"]
noncomputable def C65a : ℝ :=
  sInf {L : ℝ | ∃ C > (0 : ℝ), ∀ q ≥ 2, ∀ a : ℕ, Nat.Coprime a q →
    (leastPrime a q : ℝ) ≤ C * (q : ℝ) ^ L}

/-- The trivial lower bound $1$: for $a = 1$ the least prime in the progression is at least
$q + 1$. -/
@[category research solved, AMS 11]
theorem c65a_lower_bound : 1 ≤ C65a := by
  sorry

/-- The best known upper bound $5$, reported in [MMT2024]. Xylouris [Xyl2011] proved
$L \le 5.18$. -/
@[category research solved, AMS 11]
theorem c65a_upper_bound : C65a ≤ 5 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ico_c65a : answer(sorry) ∈ Set.Ico C65a 5 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ioc_c65a : answer(sorry) ∈ Set.Ioc 1 C65a := by
  sorry

/-- What is the exact value of the constant? It is conjectured to be $1$, which would follow
from the generalised Riemann hypothesis up to logarithmic factors. -/
@[category research open, AMS 11]
theorem c65a_eq : C65a = answer(sorry) := by
  sorry

end Constant65a
