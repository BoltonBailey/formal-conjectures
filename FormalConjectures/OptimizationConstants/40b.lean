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
# Tao's Optimization constant 40b / The asymptotic Dobrowolski constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 40b](https://teorth.github.io/optimizationproblems/constants/40b.html)
- [Dob1979] Dobrowolski, E. "On a question of Lehmer and the number of irreducible factors of a
  polynomial." Acta Arithmetica 34 (1979), 391–401.
- [CS1982] Cantor, D. C.; Straus, E. G. "On a conjecture of D. H. Lehmer." Acta Arithmetica 42
  (1982), 97–100.
- [Lou1983] Louboutin, R. "Sur la mesure de Mahler d'un nombre algébrique." Comptes Rendus de
  l'Académie des Sciences 296 (1983), 707–708.
- [Vou1996] Voutier, P. "An effective lower bound for the height of algebraic numbers."
  Acta Arithmetica 74 (1996), 81–95.

The Mahler measure is formalised in `FormalConjectures.Wikipedia.LehmerMahlerMeasureProblem`.
-/

open Polynomial
open scoped ENNReal

namespace Constant40b

/-- The Dobrowolski scale $B(d) = (\log\log d / \log d)^3$. -/
noncomputable def B (d : ℕ) : ℝ := (Real.log (Real.log d) / Real.log d) ^ 3

/-- An irreducible integer polynomial whose complex roots are not roots of unity, i.e. the
minimal polynomial of an algebraic number that is not a root of unity. -/
def NotRootOfUnity (f : ℤ[X]) : Prop :=
  Irreducible f ∧ 0 < f.natDegree ∧
    ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, ¬ ∃ m : ℕ, 0 < m ∧ z ^ m = 1

/-- The exponents $c$ for which Dobrowolski's asymptotic lower bound
$M(\alpha) \ge 1 + (c - \varepsilon)B(d)$ holds for all non-root-of-unity $\alpha$ of large
enough degree. -/
def Admissible : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∀ ε > (0 : ℝ), ∃ D : ℕ, ∀ f : ℤ[X],
    NotRootOfUnity f → D ≤ f.natDegree →
    1 + (c - ε) * B f.natDegree ≤ LehmerMahlerMeasureProblem.mahlerMeasureZ f}

/-- **Tao's Optimization constant 40b / The asymptotic Dobrowolski constant**:
the largest constant $c$ such that for every $\varepsilon > 0$ one has
$M(\alpha) \ge 1 + (c - \varepsilon)(\log\log d / \log d)^3$ for every non-root-of-unity
algebraic number $\alpha$ of sufficiently large degree $d$. It is taken in `ℝ≥0∞` because no
finite upper bound is known. -/
@[optimization_constant "40b"]
noncomputable def C40b : ℝ≥0∞ := ⨆ c ∈ Admissible, ENNReal.ofReal c

/-- Lower bound from [Dob1979] (1979). Dobrowolski proved $M(\alpha) > 1+(1-\epsilon)B(d)$ for $d\ge
d(\epsilon)$ (as reported by Voutier), hence $C_{40b}\ge 1$. [Vou1996-dob-asymp] -/
@[category research solved, AMS 11 12]
theorem c40b_lower_bound_dob1979 : 1 ≤ C40b := by
  sorry

/-- Lower bound from [CS1982] (1982). Cantor–Straus replace the coefficient $(1-\epsilon)$ by
$(2-\epsilon)$ (as reported by Voutier), hence $C_{40b}\ge 2$. [Vou1996-cs-lou] -/
@[category research solved, AMS 11 12]
theorem c40b_lower_bound_cs1982 : 2 ≤ C40b := by
  sorry

/-- Lower bound from [Lou1983] (1983). Louboutin improves the coefficient to $(\tfrac94-\epsilon)$
(as reported by Voutier), hence $C_{40b}\ge 9/4$. [Vou1996-cs-lou] -/
@[category research solved, AMS 11 12]
theorem c40b_lower_bound_lou1983 : ENNReal.ofReal (9 / 4) ≤ C40b := by
  sorry

/-- Trivial upper bound. -/
@[category research solved, AMS 11 12]
theorem c40b_upper_bound_trivial : C40b ≤ ⊤ := by
  exact le_top

/-- What is the exact value of the constant? -/
@[category research open, AMS 11 12]
theorem c40b_eq : answer(sorry) = C40b := by
  sorry

end Constant40b
