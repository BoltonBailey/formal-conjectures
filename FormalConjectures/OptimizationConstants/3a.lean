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
# Tao's Optimization constant 3a / The Gyarmati-Hennecart-Ruzsa sum-difference constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 3a](https://teorth.github.io/optimizationproblems/constants/3a.html)
- [Ru96] Ruzsa, I. Z. "Sums of finite sets." Number Theory (New York, 1991–1995), Springer
  (1996), 281–293.
- [GHR2007] Gyarmati, K.; Hennecart, F.; Ruzsa, I. Z. "Sums and differences of finite sets."
  Functiones et Approximatio 37 (2007), 175–186.
- [GGSWT2025] Georgiev, B.; Gómez-Serrano, J.; Tao, T.; Wagner, A. Z. "Mathematical exploration
  and discovery at scale." [arXiv:2511.02864](https://arxiv.org/abs/2511.02864)
- [G2025] Gerbicz, Robert. Sums and differences of sets (improvement over AlphaEvolve), 2025.
  [arXiv:2505.16105](https://arxiv.org/abs/2505.16105).
- [Z2025] Zheng, Fan. Sums and differences of sets: a further improvement over AlphaEvolve, 2025.
  [arXiv:2506.01896](https://arxiv.org/abs/2506.01896).
- [G2026] Griego, Sebastian. Base-$21$ digit construction certificate for $C_{3a}$, [submitted to
  this repository](https://github.com/teorth/optimizationproblems/pull/71) (2026).
- [MI2026] Mosaic Intelligence ([@111111](https://x.com/111111)). Exact-count certificate for
  problem 3a, [certificate archive](https://doi.org/10.5281/zenodo.20794135), [submitted to this
  repository](https://github.com/teorth/optimizationproblems/pull/95) (2026).
- [Num2026] Numaro ([numaro.tech](https://numaro.tech)). Large-deviation limit certificate for a
  base-89 capped digit construction, [certificate archive](https://doi.org/10.5281/zenodo.21504058),
  submitted to this repository (2026).
- [K2026] Kleinwaks, Logan. A masked-digit lower bound for the Gyarmati–Hennecart–Ruzsa
  sum–difference constant, [proof and verification
  package](https://github.com/kleinwaks/masked-digit-sum-difference-bound), [submitted to this
  repository](https://github.com/teorth/optimizationproblems/pull/134) (2026).
- [K2026b] Kleinwaks, Logan. Improved lower bound for the Gyarmati–Hennecart–Ruzsa sum–difference
  constant using masked digits and controlled carries, [proof, verification package, and Lean
  formalization](https://github.com/kleinwaks/masked-digit-sum-difference-bound), [submitted to this
  repository](https://github.com/teorth/optimizationproblems/pull/146) (2026).
-/

open scoped Pointwise Finset

namespace Constant3a

/-- **Tao's Optimization constant 3a / The Gyarmati-Hennecart-Ruzsa sum-difference constant**:
the largest constant $c$ for which there are arbitrarily large finite sets $A, B$ of integers
with $|A + B| \ll |A|$ and $|A - B| \gg |A + B|^c$. -/
@[optimization_constant "3a"]
noncomputable def C3a : ℝ :=
  sSup {c : ℝ | ∃ K > (0 : ℝ), ∃ κ > (0 : ℝ), ∀ N : ℕ, ∃ A B : Finset ℤ,
    N ≤ #A ∧ (#(A + B) : ℝ) ≤ K * #A ∧ κ * (#(A + B) : ℝ) ^ c ≤ #(A - B)}

/-- Trivial lower bound. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_trivial : 1 ≤ C3a := by
  sorry

/-- Lower bound from [Ru96] (1996). Elementary construction from $U = \{0,1,3\}$, which has $\lvert
U+U\rvert = 6$ and $\lvert U-U\rvert = 7$; reported in [GHR2007, §1]. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_ru96 : 2 - Real.log 6 / Real.log 7 ≤ C3a := by
  sorry

/-- Lower bound from [GHR2007] (2007). The lemma below applied to $U = \{0,1,3,6,13,17,21\}$, with
$\lvert U+U\rvert = 26$, $\lvert U-U\rvert = 39$ and $q = 43$. Found by exhaustive search to be
optimal over all $U$ with $\lvert U\rvert \le 11$. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_ghr2007_1 : 1.1078 ≤ C3a := by
  sorry

/-- Lower bound from [GHR2007] (2007). Projection to $\mathbb{Z}$ of the simplex set $V(m,L) = \{x
\in \mathbb{N}^m : x_1 + \dots + x_m \le L\}$ of [HRY1999], with $m = 8$, $L = 9$: $\lvert U+U\rvert
= 1562275$, $\lvert U-U\rvert = 23301307$, $q = 11668193551$. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_ghr2007_2 : 1.1165 ≤ C3a := by
  sorry

/-- Lower bound from [GHR2007] (2007). Same construction with $m = 9$, $L = 7$ and a greedy choice
of projection multipliers that preserves the number of sums: $\lvert U+U\rvert = \binom{23}{9} =
817190$, $\lvert U-U\rvert = 12494233$, $q = 542817927$. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_ghr2007_3 : 1.135596 ≤ C3a := by
  sorry

/-- Lower bound from [GHR2007] (2007). Theorem 1 of [GHR2007]. Same construction with $m = 11$, $L =
7$ and the condition $L_j > LL_{j-1}$ relaxed, so that a few sums and differences are lost in the
projection. See the note below on reproducing this value. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_ghr2007_4 : 1.14465 ≤ C3a := by
  sorry

/-- Lower bound from [GGSWT2025] (2025). AlphaEvolve (Problem 6.44 of [GGSWT2025]), maximizing the
lemma value below over a set $U_1$ of $2003$ integers. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_ggswt2025_1 : 1.1479 ≤ C3a := by
  sorry

/-- Lower bound from [GGSWT2025] (2025). AlphaEvolve, from a related set $U_2$ of $54265$ integers
found by running the same experiment longer. This, not $1.1479$, is the final figure reported in
[GGSWT2025, §6.25]. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_ggswt2025_2 : 1.1584 ≤ C3a := by
  sorry

/-- Lower bound from [G2025] (2025). -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_g2025 : 1.173050 ≤ C3a := by
  sorry

/-- Lower bound from [Z2025] (2025). "We construct a sequence of $U$ sets which in the limit
establishes a new lower bound of $\theta = 1.173077$"; not certified by a finite-depth computation.
-/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_z2025 : 1.173077 ≤ C3a := by
  sorry

/-- Lower bound from [G2026] (2026). Base-$21$ digit construction with exact counting certificate.
-/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_g2026 : 1.1740744 ≤ C3a := by
  sorry

/-- Lower bound from [MI2026] (2026). Base-$33$ digit construction with exact counting certificate.
-/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_mi2026 : 1.1835129324 ≤ C3a := by
  sorry

/-- Lower bound from [Num2026] (2026). Capped base-$89$ digit construction (max digit $44$, sparse
29-letter alphabet); certified as the large-deviation LIMIT of the exact per-depth lemma values
$\theta(U_d)$, each valid for every $d$ and increasing to the limit (the same limit-as-lower-bound
principle as [Z2025]); interval-arithmetic certificate, replayable checker included. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_num2026 : 1.187326127925948 ≤ C3a := by
  sorry

/-- Lower bound from [K2026] (2026). Base-$34065$ masked-digit limit construction with
$M=\langle1518,1524,1587,2024,2032,2116\rangle\cap[0,17032]$ and a directed-rounding certificate. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_k2026 : 1.19102809 ≤ C3a := by
  sorry

/-- Lower bound from [K2026b] (2026). The row lists $1.19102809$ and $1.19519192$. Lean-formalized
proof of $1.19519192$* via controlled-carry masked-digit limit construction with
$M=\langle1971,2016,2100,2628,2688,2800\rangle\cap[0,26972]$ in base $27022$ and Lean-formalized
explicit finite construction of $1.19102809$ with
$M=\langle1518,1524,1587,2024,2032,2116\rangle\cap[0,17032]$ in base $34065$ using $10^{13}$ digits.
Also includes formalization of necessary results from [GHR2007]. -/
@[category research solved, AMS 5 11]
theorem c3a_lower_bound_k2026b : 1.19519192 ≤ C3a := by
  sorry

/-- Upper bound from [GHR2007] (2007). -/
@[category research solved, AMS 5 11]
theorem c3a_upper_bound_ghr2007 : C3a ≤ 4 / 3 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c3a_eq : answer(sorry) = C3a := by
  sorry

end Constant3a
