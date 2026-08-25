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
# Tao's Optimization constant 65a / Linnik's constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 65a](https://teorth.github.io/optimizationproblems/constants/65a.html)
- [Lin1944] Linnik, Yu. V. "On the least prime in an arithmetic progression." Rec. Math.
  (Mat. Sbornik) 15 (1944), 139–178 and 347–368.
- [Xyl2011] Xylouris, T. "On the least prime in an arithmetic progression and estimates for the
  zeros of Dirichlet L-functions." Acta Arithmetica 150 (2011), 65–91.
- [MMT2024] Maynard, J.; Merikoski, J.; Thorner, J. An $L$-function-free proof of Linnik's
  theorem, 2024.
- [XylDiss2011] Xylouris, Triantafyllos. "Uber die Nullstellen der Dirichletschen L-Funktionen und
  die kleinste Primzahl in einer arithmetischen Progression." Bonner Mathematische Schriften 404,
  Universitat Bonn, Mathematisches Institut (2011). Dissertation for the degree of Doctor of
  Mathematics and Natural Sciences.
-/

namespace Constant65a

/-- The least prime in the arithmetic progression $a \bmod q$. -/
noncomputable def leastPrime (a q : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ (p : ZMod q) = (a : ZMod q)}

/-- **Tao's Optimization constant 65a / Linnik's constant**:
the infimum of the exponents $L$ for which $P(a, q) \le C q^L$ holds for all $q \ge 2$ and all
$a$ coprime to $q$, with a constant $C$ independent of $a$ and $q$. -/
@[optimization_constant "65a"]
noncomputable def C65a : ℝ :=
  sInf {L : ℝ | ∃ C > (0 : ℝ), ∀ q ≥ 2, ∀ a : ℕ, Nat.Coprime a q →
    (leastPrime a q : ℝ) ≤ C * (q : ℝ) ^ L}

/-- Trivial lower bound. Trivial: $P(1,q)\ge q+1$. -/
@[category research solved, AMS 11]
theorem c65a_lower_bound_trivial : 1 ≤ C65a := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Pan 1957). [Xyl2011-historical-table]
-/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_1 : C65a ≤ 10000 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Pan 1958). [Xyl2011-historical-table]
-/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_2 : C65a ≤ 5448 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Chen 1965).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_3 : C65a ≤ 777 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Jutila 1971).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_4 : C65a ≤ 630 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Jutila 1970).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_5 : C65a ≤ 550 := by
  sorry

/-- Upper bound from [MMT2024] (2024). New $L$-function-free proof of Linnik's problem (coarse
exponent). [MMT2024-ub-350] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_mmt2024 : C65a ≤ 350 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Chen 1977).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_6 : C65a ≤ 168 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Jutila 1977).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_7 : C65a ≤ 80 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Graham 1977).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_8 : C65a ≤ 36 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Graham 1981).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_9 : C65a ≤ 20 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Chen 1979).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_10 : C65a ≤ 17 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Wang 1986).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_11 : C65a ≤ 16 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Chen-Liu 1989).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_12 : C65a ≤ 13.5 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Chen-Liu 1991).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_13 : C65a ≤ 11.5 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Wang 1991).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_14 : C65a ≤ 8 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Historical table entry (Heath-Brown 1992).
[Xyl2011-historical-table] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_15 : C65a ≤ 5.5 := by
  sorry

/-- Upper bound from [Xyl2011] (2011). Published explicit effective exponent in Theorem 1.1.
[Xyl2011-ub-5-18] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyl2011_16 : C65a ≤ 5.18 := by
  sorry

/-- Upper bound from [XylDiss2011] (2011). Attributed in modern literature to Xylouris's 2011
dissertation. [MMT2024-ub-5] -/
@[category research solved, AMS 11]
theorem c65a_upper_bound_xyldiss2011 : C65a ≤ 5 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c65a_eq : answer(sorry) = C65a := by
  sorry

end Constant65a
