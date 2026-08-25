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

/-- Lower bound from Trivial (Kronecker). For $f\in\mathbb{Z}[x]$, one has $M(f)\ge 1$, with
$M(f)=1$ precisely in the cyclotomic/monomial case; hence $L\ge 1$. [BDM2007-kronecker] -/
@[category research solved, AMS 11 12]
theorem c40a_lower_bound_trivial : 1 ≤ C40a := by
  have h2 : LehmerMahlerMeasureProblem.mahlerMeasureZ (Polynomial.C 2) = 2 := by
    rw [LehmerMahlerMeasureProblem.mahlerMeasureZ, Polynomial.map_C,
      LehmerMahlerMeasureProblem.mahlerMeasure, Polynomial.roots_C, Polynomial.leadingCoeff_C]
    simp
  refine le_csInf ⟨2, Polynomial.C 2, by rw [h2]; norm_num, h2⟩ ?_
  rintro b ⟨f, hf, rfl⟩
  exact hf.le

/-- Upper bound from [BDM2007] [Leh1933] (2007, 1933). Lehmer’s example polynomial
$\ell(x)=x^{10}+x^9-x^7-x^6-x^5-x^4-x^3+x+1$ has Mahler measure $M(\ell)=1.176280\ldots$, giving
$L\le 1.176280\ldots$. [BDM2007-lehmer-poly] -/
@[category research solved, AMS 11 12]
theorem c40a_upper_bound_bdm2007_leh1933_1 : C40a ≤ 1.176280 := by
  sorry

/-- Upper bound from [BDM2007] [Leh1933] (2007, 1933). The value $1.176280\ldots$ (the Mahler
measure of $\ell$) “remains the smallest known measure $>1$ for an integer polynomial,” i.e. it is
the best currently known explicit upper bound for $L$. [BDM2007-smallest-known] -/
@[category research solved, AMS 11 12]
theorem c40a_upper_bound_bdm2007_leh1933_2 : C40a ≤ 1.176280 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11 12]
theorem c40a_eq : answer(sorry) = C40a := by
  sorry

end Constant40a
