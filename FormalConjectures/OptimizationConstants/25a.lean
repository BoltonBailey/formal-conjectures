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
# Tao's Optimization constant 25a / The Mahler volume product constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 25a](https://teorth.github.io/optimizationproblems/constants/25a.html)
- [BM1987] Bourgain, J.; Milman, V. D. "New volume ratio properties for convex symmetric bodies
  in $\mathbb{R}^n$." Inventiones Mathematicae 88 (1987), 319–340.
- [N2012] Nazarov, F. "The Hörmander proof of the Bourgain-Milman theorem." Geometric Aspects of
  Functional Analysis, Lecture Notes in Mathematics 2050 (2012), 335–343.
- [K2008] Kuperberg, G. "From the Mahler conjecture to Gauss linking integrals." Geometric and
  Functional Analysis 18 (2008), 870–892.
-/

open MeasureTheory
open scoped ENNReal Nat

namespace Constant25a

/-- The **polar body** of a set $K \subseteq \mathbb{R}^n$. -/
def polarBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ K, inner ℝ x y ≤ (1 : ℝ)}

/-- **Tao's Optimization constant 25a / The Mahler volume product constant**:
the largest $c$ with $n!\,\mathrm{Vol}_n(K)\,\mathrm{Vol}_n(K^\circ) \ge c^n$ for every $n$ and
every centrally symmetric convex body $K \subseteq \mathbb{R}^n$. -/
@[optimization_constant "25a"]
noncomputable def C25a : ℝ :=
  sSup {c : ℝ | 0 ≤ c ∧ ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K →
    Convex ℝ K → (interior K).Nonempty → K = -K →
      ENNReal.ofReal (c ^ n) ≤ (n ! : ℝ≥0∞) * volume K * volume (polarBody K)}

/-- The best known lower bound $\pi$, proven by Kuperberg in [K2008]. Bourgain-Milman [BM1987]
first proved that some positive constant works, and Nazarov [N2012] gave the explicit value
$\pi^3/16$. -/
@[category research solved, AMS 52]
theorem c25a_lower_bound : Real.pi ≤ C25a := by
  sorry

/-- The upper bound $4$, given by the cube $[-1, 1]^n$, whose Mahler volume is $4^n$. -/
@[category research solved, AMS 52]
theorem c25a_upper_bound : C25a ≤ 4 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ioc_c25a : answer(sorry) ∈ Set.Ioc Real.pi C25a := by
  sorry

/-- What is the exact value of the constant? The (symmetric) **Mahler conjecture** predicts that
it is $4$, with the Hanner polytopes as extremisers. -/
@[category research open, AMS 52]
theorem c25a_eq : C25a = answer(sorry) := by
  sorry

end Constant25a
