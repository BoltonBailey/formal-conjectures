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
# Tao's Optimization constant 84b / The sum-product exponent for the reals

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 84b](https://teorth.github.io/optimizationproblems/constants/84b.html)
- [ErSz83] Erdős, P.; Szemerédi, E. "On sums and products of integers." Studies in Pure
  Mathematics, Birkhäuser (1983), 213–218.
- [So09] Solymosi, J. "Bounding multiplicative energy by the sumset." Advances in Mathematics 222
  (2009), 402–408.
- [Cu25] Cushman, A. Current record lower bound, 2025.
- [BSSZ2026] Bloom, T. F.; Sawin, W.; Schildkraut, K.; Zhelezov, D. Disproof of the sum-product
  conjecture for the reals, 2026.
- [El97] Elekes, György. "On the number of sums and products". Acta Arithmetica 81 (1997), no. 4,
  365–367.
- [So05] Solymosi, József. "On the number of sums and products". Bulletin of the London Mathematical
  Society 37 (2005), no. 4, 491–494.
- [KoSh16] Konyagin, Sergei V.; Shkredov, Ilya D. "New results on sums and products in
  $\mathbb{R}$". Trudy Mat. Inst. Steklova 294 (2016), 87–98; translation in Proc. Steklov Inst.
  Math. 294 (2016), 78–88.
- [Sh19] Shakan, George. "On higher energy decompositions and the sum-product phenomenon".
  Mathematical Proceedings of the Cambridge Philosophical Society 167 (2019), no. 3, 599–617.
- [RuSt22] Rudnev, Misha; Stevens, Sophie. "An update on the sum-product problem". Mathematical
  Proceedings of the Cambridge Philosophical Society 173 (2022), no. 2, 411–430.
  [arXiv:2005.11145](https://arxiv.org/abs/2005.11145).
- [Bl25] Bloom, Thomas F. "Sum-product estimate over the reals" (2025). See [Bloom-notes] for the
  precise reference.
- [Al26] Althoefer, Ingo. "Improved constant for [BSSZ2026]". Note (28 May 2026), with
  [tex](https://althofer.de/improved_constant_052.tex) and
  [pdf](https://althofer.de/improved_constant_052.pdf).
- [EPF52] Bloom, Thomas F. (ed.). "Erdős Problem #52: Discussion thread".
  [erdosproblems.com/forum/thread/52](https://www.erdosproblems.com/forum/thread/52) (accessed 29
  May 2026).
-/

open Filter
open scoped Pointwise Finset

namespace Constant84b

/-- **Tao's Optimization constant 84b / The sum-product exponent for the reals**:
$\liminf_n \min_{|A| = n} \frac{\log \max(|A + A|, |AA|)}{\log n}$ over finite sets
$A \subseteq \mathbb{R}$. -/
@[optimization_constant "84b"]
noncomputable def C84b : ℝ :=
  liminf (fun n : ℕ => sInf {t : ℝ | ∃ A : Finset ℝ, #A = n ∧
    t = Real.log (max (#(A + A) : ℝ) (#(A * A) : ℝ)) / Real.log n}) atTop

/-- Trivial lower bound. $\lvert A+A\rvert \ge 2\lvert A\rvert - 1$. -/
@[category research solved, AMS 5 11]
theorem c84b_lower_bound_trivial : 1 ≤ C84b := by
  sorry

/-- Lower bound from [El97] (1997). Elekes, via the Szemerédi–Trotter incidence theorem. -/
@[category research solved, AMS 5 11]
theorem c84b_lower_bound_el97 : 5 / 4 ≤ C84b := by
  sorry

/-- Lower bound from [So05] (2005). Solymosi. -/
@[category research solved, AMS 5 11]
theorem c84b_lower_bound_so05 : 14 / 11 ≤ C84b := by
  sorry

/-- Lower bound from [So09] (2009). Solymosi; the long-standing "$4/3$ barrier". -/
@[category research solved, AMS 5 11]
theorem c84b_lower_bound_so09 : 4 / 3 ≤ C84b := by
  sorry

/-- Lower bound from [KoSh16] (2016). The website lists this value as approximate ($\approx
1.33338$). Konyagin–Shkredov; first to break the $4/3$ barrier (their 2015 and 2016 papers give
$\approx 1.33338$ and $\approx 1.33384$). -/
@[category research solved, AMS 5 11]
theorem c84b_lower_bound_kosh16 : 1.33338 ≤ C84b := by
  sorry

/-- Lower bound from [Sh19] (2019). The website lists this value as approximate ($\approx 1.33428$).
Shakan. -/
@[category research solved, AMS 5 11]
theorem c84b_lower_bound_sh19 : 1.33428 ≤ C84b := by
  sorry

/-- Lower bound from [RuSt22] (2005). Rudnev–Stevens. -/
@[category research solved, AMS 5 11]
theorem c84b_lower_bound_rust22 : 1558 / 1167 ≤ C84b := by
  sorry

/-- Lower bound from [Bl25] (2025). Bloom. -/
@[category research solved, AMS 5 11]
theorem c84b_lower_bound_bl25 : 1270 / 951 ≤ C84b := by
  sorry

/-- Lower bound from [Cu25] (2025). Cushman; current record. -/
@[category research solved, AMS 5 11]
theorem c84b_lower_bound_cu25 : 4 / 3 + 10 / 4407 ≤ C84b := by
  sorry

/-- Upper bound from [ErSz83] (1983). Erdős–Szemerédi constructed sets of integers with $\max(\lvert
A+A\rvert, \lvert AA\rvert) \le \lvert A\rvert^{2-c/\log\log\lvert A\rvert}$, so the exponent is
$\le 2$. This was conjectured to be sharp (the sum-product conjecture). -/
@[category research solved, AMS 5 11]
theorem c84b_upper_bound_ersz83 : C84b ≤ 2 := by
  sorry

/-- Upper bound from [BSSZ2026] (2026). The bound $2 - c$ for an absolute constant $c > 0$.
Bloom–Sawin–Schildkraut–Zhelezov disprove the conjecture by constructing arbitrarily large $A
\subset \mathbb{R}$ — algebraic integers in totally real number fields of degree $\asymp \log\lvert
A\rvert$ — with $\max(\lvert A+A\rvert, \lvert AA\rvert) \le \lvert A\rvert^{2-c}$. A non-optimized
explicit version of the argument gives $c \ge 0.00000087$, i.e. exponent $\le 1.99999913$ (the
authors stress this value "should not be taken too seriously"). -/
@[category research solved, AMS 5 11]
theorem c84b_upper_bound_bssz2026 : C84b < 2 := by
  sorry

/-- Upper bound from [Al26], [EPF52] (2026). Althoefer (28 May 2026), posted on the Erdős Problems
forum [EPF52]; a ChatGPT 5.5 long-thinking optimization of the explicit constant of [BSSZ2026, §5]
giving $c \ge 0.000719$. Unverified. -/
@[category research solved, AMS 5 11]
theorem c84b_upper_bound_al26_epf52 : C84b ≤ 1.999281 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c84b_eq : answer(sorry) = C84b := by
  sorry

end Constant84b
