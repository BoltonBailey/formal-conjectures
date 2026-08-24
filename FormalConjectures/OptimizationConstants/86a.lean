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
# Tao's Optimization constant 86a / The Schur-Siegel-Smyth trace constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 86a](https://teorth.github.io/optimizationproblems/constants/86a.html)
- [Sch18] Schur, I. "Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit
  ganzzahligen Koeffizienten." Mathematische Zeitschrift 1 (1918), 377–402.
- [Smy84] Smyth, C. J. "The mean values of totally real algebraic integers." Mathematics of
  Computation 42 (1984), 663–681.
- [Smi24] Smith, A. "Algebraic integers with conjugates in a prescribed distribution." Annals of
  Mathematics 200 (2024), 249–299.
- [SO24] Serre-type explicit measures optimised by gradient descent, 2024.
- [OSS25] Orloski, A.; Sardari, N. T.; Smith, A. Logarithmic-energy constraints in Smyth's
  linear program, 2025.
-/

open Polynomial

namespace Constant86a

/-- A monic integer polynomial is the minimal polynomial of a **totally positive** algebraic
integer exactly when it is irreducible of positive degree and all of its complex roots are real
and strictly positive. -/
def IsTotallyPositive (f : ℤ[X]) : Prop :=
  f.Monic ∧ Irreducible f ∧ 0 < f.natDegree ∧
    ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z.im = 0 ∧ 0 < z.re

/-- The **absolute trace** (trace-to-degree ratio) of the algebraic integer with minimal
polynomial $f$ of degree $d$, namely $-a_{d-1}/d$. -/
noncomputable def absTrace (f : ℤ[X]) : ℝ :=
  -(f.coeff (f.natDegree - 1) : ℝ) / f.natDegree

/-- **Tao's Optimization constant 86a / The Schur-Siegel-Smyth trace constant**:
the smallest limit point of the absolute traces of totally positive algebraic integers,
equivalently the supremum of the $\rho \ge 0$ for which all but finitely many totally positive
algebraic integers $\alpha$ satisfy $\mathrm{tr}(\alpha) \ge \rho \deg(\alpha)$. -/
@[optimization_constant "86a"]
noncomputable def C86a : ℝ :=
  sSup {ρ : ℝ | 0 ≤ ρ ∧ {f : ℤ[X] | IsTotallyPositive f ∧ absTrace f < ρ}.Finite}

/-- The best known lower bound $1.80203$, proven by Orloski-Sardari-Smith in [OSS25]. Schur
[Sch18] gave $\sqrt{e} \approx 1.6487$ and Smyth's auxiliary function method [Smy84] gave
$1.7719$. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound : 1.80203 ≤ C86a := by
  sorry

/-- The best known upper bound $1.8216$ [SO24]. Smith [Smi24] proved the constant is strictly
less than $2$, disproving the long-standing conjecture that it equals $2$. -/
@[category research solved, AMS 11 12]
theorem c86a_upper_bound : C86a ≤ 1.8216 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11 12]
theorem mem_Ico_c86a : answer(sorry) ∈ Set.Ico C86a 1.8216 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11 12]
theorem mem_Ioc_c86a : answer(sorry) ∈ Set.Ioc 1.80203 C86a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11 12]
theorem c86a_eq : C86a = answer(sorry) := by
  sorry

end Constant86a
