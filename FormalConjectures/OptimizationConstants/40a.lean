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
import FormalConjectures.Wikipedia.LehmerMahlerMeasureProblem

/-!
# Tao's Optimization constant 40a / Lehmer's Mahler measure constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 40a](https://teorth.github.io/optimizationproblems/constants/40a.html)
- [Leh1933] Lehmer, D. H. "Factorization of certain cyclotomic functions." Annals of Mathematics
  34 (1933), 461–479.
- [BDM2007] Borwein, P.; Dobrowolski, E.; Mossinghoff, M. J. "Lehmer's problem for polynomials
  with odd coefficients." Annals of Mathematics 166 (2007), 347–366.

The Mahler measure is formalised in `FormalConjectures.Wikipedia.LehmerMahlerMeasureProblem`.
-/

open Polynomial

namespace Constant40a

/-- **Tao's Optimization constant 40a / Lehmer's Mahler measure constant**:
the infimum of the Mahler measures $M(f) > 1$ of integer polynomials $f$. Lehmer's question
asks whether this infimum is $1$. -/
@[optimization_constant "40a"]
noncomputable def C40a : ℝ :=
  sInf {LehmerMahlerMeasureProblem.mahlerMeasureZ f |
    (f : ℤ[X]) (_ : 1 < LehmerMahlerMeasureProblem.mahlerMeasureZ f)}

/-- The trivial lower bound $1$, which follows from Kronecker's theorem. -/
@[category research solved, AMS 11 12]
theorem c40a_lower_bound : 1 ≤ C40a := by
  sorry

/-- The best known upper bound $1.176280\ldots$, the Mahler measure of Lehmer's polynomial
$x^{10} + x^9 - x^7 - x^6 - x^5 - x^4 - x^3 + x + 1$ [Leh1933], [BDM2007]. -/
@[category research solved, AMS 11 12]
theorem c40a_upper_bound :
    C40a ≤ LehmerMahlerMeasureProblem.mahlerMeasureZ
      LehmerMahlerMeasureProblem.lehmerPolynomial := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11 12]
theorem mem_Ico_c40a :
    answer(sorry) ∈ Set.Ico C40a (LehmerMahlerMeasureProblem.mahlerMeasureZ
      LehmerMahlerMeasureProblem.lehmerPolynomial) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11 12]
theorem mem_Ioc_c40a : answer(sorry) ∈ Set.Ioc 1 C40a := by
  sorry

/-- What is the exact value of the constant? **Lehmer's conjecture** is that it equals the
Mahler measure of Lehmer's polynomial; in particular that it is strictly larger than $1$. -/
@[category research open, AMS 11 12]
theorem c40a_eq : C40a = answer(sorry) := by
  sorry

end Constant40a
