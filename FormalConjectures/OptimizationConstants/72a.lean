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

/-- Trivial lower bound. Trivial from nonnegativity of the defining infimum. -/
@[category research solved, AMS 11]
theorem c72a_lower_bound_trivial : 0 ≤ C72a := by
  sorry

/-- Upper bound from [Pom2011] (2009). Primitive characters, explicit inequality; asymptotically
this gives $c=2/\pi^2$ (even) and $c=1/(2\pi)$ (odd), so $C_{72}\le 2/\pi^2$. [Pom2011-thm1] -/
@[category research solved, AMS 11]
theorem c72a_upper_bound_pom2011 : C72a ≤ 2 / (Real.pi ^ 2) := by
  sorry

/-- Upper bound from [B2022] (2022). All primitive moduli (hence also squarefree), odd characters;
gives $C_{72}^{\mathrm{odd}}\le 3/(8\pi)$ and thus $C_{72}\le 3/(8\pi)$. [B2022-main] -/
@[category research solved, AMS 11]
theorem c72a_upper_bound_b2022 : C72a ≤ 3 / (8 * Real.pi) := by
  sorry

/-- Upper bound from [Kerr2020] (1807). Cubefree moduli (hence squarefree), arbitrary intervals;
implies the same leading constant for the initial-interval quantity $S(\chi)$. [Kerr2020-main] -/
@[category research solved, AMS 11]
theorem c72a_upper_bound_kerr2020 : C72a ≤ 1 / (Real.pi ^ 2) := by
  sorry

/-- Upper bound from [BK2020] (1909). Squarefree moduli, odd characters; this controls
$C_{72}=\max\{C_{72}^{\mathrm{even}},C_{72}^{\mathrm{odd}}\}$. [BK2020-main-constants] -/
@[category research solved, AMS 11]
theorem c72a_upper_bound_bk2020_1 : C72a ≤ 1 / (4 * Real.pi) := by
  sorry

/-- Upper bound from [BK2020] (1909). Squarefree moduli, even characters. [BK2020-main-constants] -/
@[category research solved, AMS 11]
theorem c72a_upper_bound_bk2020_2 : C72a ≤ 1 / (2 * Real.pi ^ 2) := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c72a_eq : answer(sorry) = C72a := by
  sorry

end Constant72a
