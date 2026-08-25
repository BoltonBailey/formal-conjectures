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
# Tao's Optimization constant 87a / Martinet's constant for totally real number fields

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 87a](https://teorth.github.io/optimizationproblems/constants/87a.html)
- [GS1964] Golod, E. S.; Shafarevich, I. R. "On the class field tower." Izv. Akad. Nauk SSSR Ser.
  Mat. 28 (1964), 261–272.
- [Mar1978] Martinet, J. "Tours de corps de classes et estimations de discriminants."
  Inventiones Mathematicae 44 (1978), 65–73.
- [Odl1990] Odlyzko, A. M. "Bounds for discriminants and related estimates for class numbers,
  regulators and zeros of zeta functions: a survey of recent results." Séminaire de Théorie des
  Nombres de Bordeaux 2 (1990), 119–141.
- [HMR2019] Hajir, F.; Maire, C.; Ramakrishna, R. "Cutting towers of number fields." 2019.
- [HM2002] Hajir, Farshid; Maire, Christian. "Tamely ramified towers and discriminant bounds for
  number fields — II." Journal of Symbolic Computation 33 (2002), no. 4, 415–423. DOI:
  [10.1006/jsco.2001.0514](https://doi.org/10.1006/jsco.2001.0514).
- [Mar2006] Martin, John S. "Improved root-discriminant bounds via ramification-restricted
  class-field towers." (2006). Cited as "Martin [25]" in [HMR2019]; specific bibliographic details
  should be verified.
-/

open NumberField

namespace Constant87a

/-- The **root discriminant** $\mathrm{rd}(K) = |\Delta_K|^{1/[K : \mathbb{Q}]}$ of a number
field. -/
noncomputable def rootDiscriminant (K : Type) [Field K] [NumberField K] : ℝ :=
  |(discr K : ℝ)| ^ ((Module.finrank ℚ K : ℝ)⁻¹)

/-- **Tao's Optimization constant 87a / Martinet's constant for totally real number fields**:
the smallest $\alpha$ such that there are totally real number fields of arbitrarily large degree
with root discriminant at most $\alpha + \varepsilon$, for every $\varepsilon > 0$. -/
@[optimization_constant "87a"]
noncomputable def C87a : ℝ :=
  sInf {α : ℝ | ∀ ε > (0 : ℝ), ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K),
    IsTotallyReal K ∧ N ≤ Module.finrank ℚ K ∧ rootDiscriminant K ≤ α + ε}

/-- Trivial lower bound. $\Delta_K \ge 1$ for every number field. -/
@[category research solved, AMS 11]
theorem c87a_lower_bound_trivial : 1 ≤ C87a := by
  sorry

/-- Lower bound from [Odl1990] (1990). Unconditional Odlyzko lower bound on the root discriminant of
any totally real number field of large degree. -/
@[category research solved, AMS 11]
theorem c87a_lower_bound_odl1990_1 : 60.8395 ≤ C87a := by
  sorry

/-- Lower bound from [Odl1990] (1990). GRH-conditional Odlyzko–Serre lower bound in the totally real
signature. -/
@[category research solved, AMS 11]
theorem c87a_lower_bound_odl1990_2 : 215.333 ≤ C87a := by
  sorry

/-- Upper bound from [Mar1978] (1978). Martinet's original construction of infinite $2$-class field
towers of totally real number fields. -/
@[category research solved, AMS 11]
theorem c87a_upper_bound_mar1978 : C87a ≤ 1058.565 := by
  sorry

/-- Upper bound from [HM2002] (2001). Hajir–Maire, refined Golod–Shafarevich with tame ramification.
-/
@[category research solved, AMS 11]
theorem c87a_upper_bound_hm2002 : C87a ≤ 954.293 := by
  sorry

/-- Upper bound from [Mar2006] (2019). Martin, further refinement of the [HM2002] construction; the
degree-$8$ field of [HMR2019, §3.3.1] has discriminant $3^4\cdot 5^4\cdot 7^4\cdot 13^2\cdot
29^4\cdot 53^2\cdot 109^2$ and root discriminant $< 913.4927$. -/
@[category research solved, AMS 11]
theorem c87a_upper_bound_mar2006 : C87a ≤ 913.493 := by
  sorry

/-- Upper bound from [HMR2019] (2019). Hajir–Maire–Ramakrishna, "cutting towers" via the refined
Golod–Shafarevich criterion. The totally real example [HMR2019, §3.3.3] is a *degree-$12$* field
$\mathrm{K}$ with $\mathrm{rd}\_{\mathrm{K}} < 770.6432$, cut at a single prime above $13$ of norm
$13$, giving $\mathrm{rd}\_{\mathrm{K}\_S^{[1]}} = \mathrm{rd}\_{\mathrm{K}}\cdot
13^{\frac{1}{12}(1-\frac{1}{2})} < 857.5662\dots$ — a saving of a factor $13^{1/24}$. Current
record. -/
@[category research solved, AMS 11]
theorem c87a_upper_bound_hmr2019 : C87a ≤ 857.567 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c87a_eq : answer(sorry) = C87a := by
  sorry

end Constant87a
