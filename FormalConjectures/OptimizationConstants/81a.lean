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
# Tao's Optimization constant 81a / Brun's constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 81a](https://teorth.github.io/optimizationproblems/constants/81a.html)
- [Bru1919] Brun, V. "La série $1/5 + 1/7 + 1/11 + 1/13 + \ldots$ où les dénominateurs sont
  nombres premiers jumeaux est convergente ou finie." Bulletin des Sciences Mathématiques 43
  (1919), 100–104 and 124–128.
- [PT2018] Platt, D.; Trudgian, T. "Improved bounds on Brun's constant." 2018.
  [arXiv:1803.01925](https://arxiv.org/abs/1803.01925)
- [N1995] Nicely, Thomas. [Enumeration to 1e14 of the twin primes and Brun's
  constant](https://faculty.lynchburg.edu/~nicely/twins/twins.html). (The Lynchburg pages return 404
  as of 17 August 2026; the author died in 2019 and the trnicely.net domain has since been taken
  over by an unrelated site, so it is not a substitute.)
- [N2010] Nicely, Thomas. [Enumeration of the twin-prime pairs from 1e16 to
  2e16](https://faculty.lynchburg.edu/~nicely/twins/t2_0001.html). (Also 404 as of 17 August 2026.)
- [CP2005] Crandall, Richard and Pomerance, Carl. "Prime Numbers: A Computational Perspective",
  second edition, Springer, New York, 2005.
- [K2007] Klyve, Dominic. [Explicit Bounds on Twin Primes and Brun’s
  Constant](https://doi.org/10.1349/ddlp.153). PhD thesis, Dartmouth College.
- [D2025] Dunn, Lachlan. [Improved upper bound on Brun's constant under
  GRH](https://doi.org/10.1017/S0004972725100233). Bulletin of the Australian Mathematical Society
  113 (2025), no. 2, 293–303; [arXiv:2504.15658](https://arxiv.org/abs/2504.15658).
-/

namespace Constant81a

/-- **Tao's Optimization constant 81a / Brun's constant**:
the sum of the reciprocals of the twin primes, $\sum_p (1/p + 1/(p+2))$ over primes $p$ such
that $p + 2$ is also prime. The series converges by Brun's theorem [Bru1919]. -/
@[optimization_constant "81a"]
noncomputable def C81a : ℝ :=
  ∑' p : {p : ℕ // p.Prime ∧ (p + 2).Prime}, ((p : ℝ)⁻¹ + ((p : ℝ) + 2)⁻¹)

/-- Lower bound from [N1995] (2019). A lower bound is just a partial sum, since $B$ is a sum of
positive terms; this one comes from the enumeration to $10^{14}$ of that reference. The much-quoted
$B \approx 1.902$ from the same computations is an extrapolation, not a bound. This enumeration led
to the discovery of the Pentium FDIV bug. -/
@[category research solved, AMS 11]
theorem c81a_lower_bound_n1995 : 1.8267324395006 ≤ C81a := by
  sorry

/-- Lower bound from [N2010] (2026). Continues the same enumeration through the twin-prime pairs
from $10^{16}$ to $2\cdot 10^{16}$. -/
@[category research solved, AMS 11]
theorem c81a_lower_bound_n2010 : 1.83180806343237901198 ≤ C81a := by
  sorry

/-- Lower bound from [PT2018] (1803). Unconditional, and the value carried in the README table. -/
@[category research solved, AMS 11]
theorem c81a_lower_bound_pt2018 : 1.840503 ≤ C81a := by
  sorry

/-- Upper bound from [CP2005] (2005). The first rigorous upper bound, from the Crandall--Pomerance
argument; attributed as such in [PT2018, §1]. -/
@[category research solved, AMS 11]
theorem c81a_upper_bound_cp2005 : C81a ≤ 2.347 := by
  sorry

/-- Upper bound from [K2007] (2007). **Conditional on the Generalised Riemann Hypothesis.** [PT2018,
§1] records this as "under the assumption of the Generalised Riemann Hypothesis we have $B <
2.1754$", so it is not comparable with the unconditional rows. Superseded under the same hypothesis
by [D2025], which notes that Klyve "never published his result, and utilized numerical integration
to calculate his subsequent bound". -/
@[category research solved, AMS 11]
theorem c81a_upper_bound_k2007 : C81a ≤ 2.175398 := by
  sorry

/-- Upper bound from [PT2018] (1803). Unconditional, and the value carried in the README table.
Sharpens the Crandall--Pomerance bound by about 13%. -/
@[category research solved, AMS 11]
theorem c81a_upper_bound_pt2018 : C81a ≤ 2.288513 := by
  sorry

/-- Upper bound from [D2025] (2025). **Conditional on the Generalised Riemann Hypothesis**, and the
best conditional bound known. Theorem 1.1: "Assume GRH. Then, $B < 2.1594$." Dunn describes this as
"the first mathematically rigorous upper bound on $B$ assuming GRH", the earlier [K2007] bound being
unpublished and resting on numerical integration. -/
@[category research solved, AMS 11]
theorem c81a_upper_bound_d2025 : C81a ≤ 2.1594 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c81a_eq : answer(sorry) = C81a := by
  sorry

end Constant81a
