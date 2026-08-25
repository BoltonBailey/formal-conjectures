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
# Tao's Optimization constant 8a / The classical zero-free region constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 8a](https://teorth.github.io/optimizationproblems/constants/8a.html)
- [dlVP1899] de la Vallée Poussin, C.-J. "Sur la fonction $\zeta(s)$ de Riemann et le nombre des
  nombres premiers inférieurs à une limite donnée." Mém. Couronnés Acad. Roy. Belgique 59 (1899).
- [MTY2022] Mossinghoff, M. J.; Trudgian, T. S.; Yang, A. "Explicit zero-free regions for the
  Riemann zeta-function." 2022.
- [BTY2026] Bellotti, C.; Trudgian, T. S.; Yang, A. Improved explicit zero-free region, 2026.
- [RS1962] Rosser, J. Barkley; Schoenfeld, Lowell. Approximate formulas for some functions of prime
  numbers. Illinois Journal of Mathematics, 6(1):64-94, 1962.
- [S1970] Stechkin, S. B. Zeros of the Riemann zeta-function. Mathematical notes of the Academy of
  Sciences of the USSR, 8(4):706-711, 1970.
- [F2002] Ford, Kevin. Vinogradov's integral and bounds for the Riemann zeta function. Proceedings
  of the London Mathematical Society, 85(3):565-633, 2002.
- [K2005] Kadiri, Habiba. Une région explicite sans zéros pour la fonction ζ de Riemann. Acta
  Arithmetica, 117(4):303-339, 2005.
- [JK2014] Jang, Won-Jin; Kwon, Seunghyun. A note on Kadiri's explicit zero free region for Riemann
  zeta function. Journal of the Korean Mathematical Society, 51(6):1291-1304, 2014.
- [MT2014] Mossinghoff, Michael J.; Trudgian, Timothy S. Nonnegative trigonometric polynomials and a
  zero-free region for the Riemann zeta-function. Journal of Number Theory, 157:329-349, 2015.
-/

open Filter

namespace Constant8a

/-- **Tao's Optimization constant 8a / The classical zero-free region constant**:
the least $R$ such that the Riemann zeta function has no zero $\sigma + it$ with $|t| \ge 2$ and
$\sigma > 1 - \frac{1}{R \log |t|}$. -/
@[optimization_constant "8a"]
noncomputable def C8a : ℝ :=
  sInf {R : ℝ | 0 < R ∧ ∀ s : ℂ, riemannZeta s = 0 → 2 ≤ |s.im| →
    s.re ≤ 1 - 1 / (R * Real.log |s.im|)}

/-- Lower bound (no reference is given on the website). The bound $2/\log \gamma_1 \approx
0.755106$, where $\gamma_1 = 14.1347\ldots$ is the ordinate of the lowest zero of $\zeta$; stated
here with the truncation $0.7551$. Optimal assuming RH -/
@[category research solved, AMS 11]
theorem c8a_lower_bound_unreferenced : 0.7551 ≤ C8a := by
  sorry

/-- Upper bound from [dlVP1899] (1899). Implies the prime number theorem -/
@[category research solved, AMS 11]
theorem c8a_upper_bound_dlvp1899 : C8a ≤ 34.82 := by
  sorry

/-- Upper bound from [RS1962] (1962). -/
@[category research solved, AMS 11]
theorem c8a_upper_bound_rs1962 : C8a ≤ 19 := by
  sorry

/-- Upper bound from [S1970] (1970). -/
@[category research solved, AMS 11]
theorem c8a_upper_bound_s1970 : C8a ≤ 9.64591 := by
  sorry

/-- Upper bound from [F2002] (2002). -/
@[category research solved, AMS 11]
theorem c8a_upper_bound_f2002 : C8a ≤ 8.463 := by
  sorry

/-- Upper bound from [K2005] (2005). -/
@[category research solved, AMS 11]
theorem c8a_upper_bound_k2005 : C8a ≤ 5.69693 := by
  sorry

/-- Upper bound from [JK2014] (2014). -/
@[category research solved, AMS 11]
theorem c8a_upper_bound_jk2014 : C8a ≤ 5.68371 := by
  sorry

/-- Upper bound from [MT2014] (2015). -/
@[category research solved, AMS 11]
theorem c8a_upper_bound_mt2014 : C8a ≤ 5.5666305 := by
  sorry

/-- Upper bound from [MTY2022] (2022). -/
@[category research solved, AMS 11]
theorem c8a_upper_bound_mty2022 : C8a ≤ 5.558691 := by
  sorry

/-- Upper bound from [BTY2026] (2026). Bellotti–Trudgian–Yang: $\zeta(\sigma+it)\ne 0$ for $t\ge 3$
and $\sigma > 1 - 1/(4.896\log t)$; extends to $\lvert t\rvert \ge 2$ using verified RH up to $H =
3\cdot 10^{12}$. A companion Theorem 2 sharpens the constant further to $4.8594$ conditionally on
unpublished improvements to prior inputs. -/
@[category research solved, AMS 11]
theorem c8a_upper_bound_bty2026 : C8a ≤ 4.896 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c8a_eq : answer(sorry) = C8a := by
  sorry

-- Note: the website lists a "trivial upper bound $0$", which contradicts the lower bound
-- $2/\log \gamma_1$ and is presumably meant as a trivial lower bound; it is not formalised here.

end Constant8a
