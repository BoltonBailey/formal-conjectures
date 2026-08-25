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
# Tao's Optimization constant 7a / The irrationality measure of $\pi$

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 7a](https://teorth.github.io/optimizationproblems/constants/7a.html)
- [D1842] Dirichlet, G. L. "Verallgemeinerung eines Satzes aus der Lehre von den
  Kettenbrüchen nebst einigen Anwendungen auf die Theorie der Zahlen." 1842.
- [M1953] Mahler, K. "On the approximation of $\pi$." Indagationes Mathematicae 15 (1953),
  30–42.
- [S2008] Salikhov, V. K. "On the irrationality measure of $\pi$." Russian Mathematical Surveys
  63 (2008), 570–572.
- [ZZ2020] Zeilberger, D.; Zudilin, W. "The irrationality measure of $\pi$ is at most
  7.103205334137\ldots" Moscow Journal of Combinatorics and Number Theory 9 (2020), 407–419.
  [arXiv:1912.06345](https://arxiv.org/abs/1912.06345)
- [Mi1974] Mignotte, M. "Approximations rationnelles de $\pi$ et quelques autres nombres". Mém. Soc.
  Math. France 37 (1974), 121–132.
- [C1982] Chudnovsky, G. V. "Hermite–Padé approximations to exponential functions and elementary
  estimates of the measure of irrationality of $\pi$". In: Lecture Notes in Mathematics 925,
  Springer (1982), 299–322.
- [RV1993] Rhin, G.; Viola, C. "On the irrationality measure of $\zeta(2)$". Ann. Inst. Fourier
  (Grenoble) 43 (1993), no. 1.
- [H1993] Hata, M. "Rational approximations to $\pi$ and some other numbers". Acta Arith. 63 (1993),
  no. 4, 335–349.

The predicate `LiouvilleWith p x` of Mathlib says that $|x - m/n| < C/n^p$ has infinitely many
solutions for some constant $C$, so the irrationality measure of $x$ is the supremum of the
exponents $p$ with `LiouvilleWith p x`.
-/

open Real

namespace Constant7a

/-- The **irrationality measure** of a real number $x$: the supremum of the exponents $p$ for
which $|x - m/n| < C/n^p$ has infinitely many solutions, for some constant $C$. -/
noncomputable def irrationalityMeasure (x : ℝ) : ℝ := sSup {p : ℝ | LiouvilleWith p x}

/-- **Tao's Optimization constant 7a / The irrationality measure of $\pi$**. -/
@[optimization_constant "7a"]
noncomputable def C7a : ℝ := irrationalityMeasure π

/-- Lower bound from [D1842] (1842). Dirichlet's theorem; holds for every irrational number (in
particular for $\pi$). -/
@[category research solved, AMS 11]
theorem c7a_lower_bound_d1842 : 2 ≤ C7a := by
  sorry

/-- Upper bound from [M1953] (1953). First proof that $C_{7a}$ is finite (i.e. $\pi$ is not a
Liouville number). -/
@[category research solved, AMS 11]
theorem c7a_upper_bound_m1953 : C7a ≤ 42 := by
  sorry

/-- Upper bound from [Mi1974] (1974). Improves Mahler's exponent. -/
@[category research solved, AMS 11]
theorem c7a_upper_bound_mi1974 : C7a ≤ 20.6 := by
  sorry

/-- Upper bound from [C1982] (1982). Uses Hermite–Padé approximation methods. -/
@[category research solved, AMS 11]
theorem c7a_upper_bound_c1982 : C7a ≤ 19.8899944 := by
  sorry

/-- Upper bound from [RV1993] (1993). Follows from an effective irrationality measure for
$\zeta(2)=\pi^2/6$. -/
@[category research solved, AMS 11]
theorem c7a_upper_bound_rv1993 : C7a ≤ 14.797074 := by
  sorry

/-- Upper bound from [H1993] (1993). Record for many years (Hata gave a series of improvements). -/
@[category research solved, AMS 11]
theorem c7a_upper_bound_h1993 : C7a ≤ 8.016045 := by
  sorry

/-- Upper bound from [S2008] (2008). Salikhov's bound. -/
@[category research solved, AMS 11]
theorem c7a_upper_bound_s2008 : C7a ≤ 7.606308 := by
  sorry

/-- Upper bound from [ZZ2020] (1912). Current record bound. -/
@[category research solved, AMS 11]
theorem c7a_upper_bound_zz2020 : C7a ≤ 7.103205334137 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c7a_eq : answer(sorry) = C7a := by
  sorry

end Constant7a
