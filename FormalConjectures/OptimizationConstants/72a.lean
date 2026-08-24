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
# Tao's Optimization constant 72a / The Pólya-Vinogradov best constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 72a](https://teorth.github.io/optimizationproblems/constants/72a.html)
- [Pom2011] Pomerance, C. "Remarks on the Pólya-Vinogradov inequality." Integers 11 (2011),
  531–542.
- [Kerr2020] Kerr, B. Character sums over cubefree moduli, 2020.
- [BK2020] Bordignon, M.; Kerr, B. "An explicit Pólya-Vinogradov inequality via partial Gaussian
  sums." Transactions of the American Mathematical Society 373 (2020), 6503–6527.
- [B2022] Bordignon, M. Odd primitive characters, 2022.
-/

open Filter

namespace Constant72a

/-- The maximal initial character sum $S(\chi) = \max_{N \le q} |\sum_{n \le N} \chi(n)|$. -/
noncomputable def charSum (q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ⨆ N : Fin (q + 1), ‖∑ n ∈ Finset.Icc 1 (N : ℕ), χ n‖

/-- The infimum of the admissible leading constants for primitive characters modulo squarefree
$q$ of a fixed parity: `sign = 1` for even characters and `sign = -1` for odd ones. -/
noncomputable def leadingConstant (sign : ℂ) : ℝ :=
  sInf {c : ℝ | ∀ ε > (0 : ℝ), ∀ᶠ q : ℕ in atTop, Squarefree q →
    ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ (-1) = sign →
      charSum q χ ≤ (c + ε) * Real.sqrt q * Real.log q}

/-- **Tao's Optimization constant 72a / The Pólya-Vinogradov best constant**:
$\max(C^{\mathrm{even}}, C^{\mathrm{odd}})$, where each is the infimum of the constants $c$ with
$S(\chi) \le (c + o(1))\sqrt q \log q$ for primitive characters of that parity modulo squarefree
$q$. -/
@[optimization_constant "72a"]
noncomputable def C72a : ℝ := max (leadingConstant 1) (leadingConstant (-1))

/-- The trivial lower bound $0$. -/
@[category research solved, AMS 11]
theorem c72a_lower_bound : 0 ≤ C72a := by
  sorry

/-- The best known upper bound $\frac{1}{4\pi}$, proven by Bordignon-Kerr in [BK2020] for odd
characters modulo squarefree $q$; the even case gives the smaller constant
$\frac{1}{2\pi^2}$. Pomerance [Pom2011] gave $2/\pi^2$. -/
@[category research solved, AMS 11]
theorem c72a_upper_bound : C72a ≤ 1 / (4 * Real.pi) := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ico_c72a : answer(sorry) ∈ Set.Ico C72a (1 / (4 * Real.pi)) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11]
theorem mem_Ioc_c72a : answer(sorry) ∈ Set.Ioc 0 C72a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c72a_eq : C72a = answer(sorry) := by
  sorry

end Constant72a
