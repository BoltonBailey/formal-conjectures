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

/-- Lower bound from [BM1987] (1987). A non-explicit positive constant $c > 0$. Bourgain–Milman
(reverse Santaló inequality): there exists a universal constant $c>0$ with $M(K)\ge c^n$ for all
centrally symmetric convex bodies $K$. -/
@[category research solved, AMS 52]
theorem c25a_lower_bound_bm1987 : 0 < C25a := by
  sorry

/-- Lower bound from [N2012] (2012). Nazarov obtained an explicit constant in the symmetric
Bourgain–Milman inequality (via a Hörmander/$\bar\partial$ method). -/
@[category research solved, AMS 52]
theorem c25a_lower_bound_n2012 : Real.pi ^ 3 / 16 ≤ C25a := by
  sorry

/-- Lower bound from [K2008] (2008). Best known explicit constant to date (Kuperberg). -/
@[category research solved, AMS 52]
theorem c25a_lower_bound_k2008 : Real.pi ≤ C25a := by
  sorry

/-- Trivial upper bound. For the cube $B_\infty^n=[-1,1]^n$ one has $\mathrm{Vol}(B_\infty^n)=2^n$
and $\mathrm{Vol}\big((B_\infty^n)^\circ\big)=2^n/n!$, hence $M(B_\infty^n)=4^n$ and $C_{25}\le 4$.
Conjecturally, this is sharp (Mahler conjecture). -/
@[category research solved, AMS 52]
theorem c25a_upper_bound_trivial : C25a ≤ 4 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 52]
theorem c25a_eq : answer(sorry) = C25a := by
  sorry

end Constant25a
