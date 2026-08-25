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
# Tao's Optimization constant 3c / The 4-slope Kakeya-type sum-difference constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 3c](https://teorth.github.io/optimizationproblems/constants/3c.html)
- [KT1999] Katz, N. H.; Tao, T. "Bounds on arithmetic projections, and applications to the
  Kakeya conjecture." Mathematical Research Letters 6 (1999), 625–630.
- [L2015] Łaba, I. Lower bound construction, 2015.
- [GGSWT2025] Georgiev, B.; Gómez-Serrano, J.; Tao, T.; Wagner, A. Z. "Mathematical exploration
  and discovery at scale." [arXiv:2511.02864](https://arxiv.org/abs/2511.02864)
- [MI2026] Entropy construction on a 95-point support, 2026.
- [A2026] Astor, T. Improved Arithmetic Kakeya-Type Counterexamples. TBA (2026)
- [G2026] Griego, Sebastian. 26-point entropy certificate for $C_{3c}$, [submitted to this
  repository](https://github.com/teorth/optimizationproblems/pull/70) (2026).

This is the four-slope analogue of `FormalConjectures.OptimizationConstants.«3b»`.
-/

open scoped Pointwise Finset

namespace Constant3c

/-- **Tao's Optimization constant 3c / The 4-slope Kakeya-type sum-difference constant**:
the least exponent $c$ such that
$|A \stackrel{G}{-} B| \le \max(|A|, |B|, |A \stackrel{G}{+} B|, |A \stackrel{G}{+} 2B|)^c$
for all finite $A, B \subseteq \mathbb{R}$ and all $G \subseteq A \times B$, where
$A \stackrel{G}{\pm} rB := \{a \pm rb : (a, b) \in G\}$. -/
@[optimization_constant "3c"]
noncomputable def C3c : ℝ :=
  sInf {c : ℝ | ∀ (A B : Finset ℝ) (G : Finset (ℝ × ℝ)), G ⊆ A ×ˢ B →
    (#(G.image fun p => p.1 - p.2) : ℝ) ≤
      max (max (max (#A : ℝ) (#B : ℝ)) (#(G.image fun p => p.1 + p.2) : ℝ))
        (#(G.image fun p => p.1 + 2 * p.2) : ℝ) ^ c}

/-- Lower bound from [L2015] (2015). -/
@[category research solved, AMS 5 11 42]
theorem c3c_lower_bound_l2015 : 1.61226 ≤ C3c := by
  sorry

/-- Lower bound from [GGSWT2025] (2025). -/
@[category research solved, AMS 5 11 42]
theorem c3c_lower_bound_ggswt2025 : 1.668 ≤ C3c := by
  sorry

/-- Lower bound from [A2026] (2026). -/
@[category research solved, AMS 5 11 42]
theorem c3c_lower_bound_a2026 : 1.67471 ≤ C3c := by
  sorry

/-- Lower bound from [G2026] (2026). Entropy construction on a 26-point support. -/
@[category research solved, AMS 5 11 42]
theorem c3c_lower_bound_g2026 : 1.67473389 ≤ C3c := by
  sorry

/-- Lower bound from [MI2026] (2026). Entropy construction on a 95-point support. -/
@[category research solved, AMS 5 11 42]
theorem c3c_lower_bound_mi2026 : 1.6747338950208249 ≤ C3c := by
  sorry

/-- Trivial upper bound. -/
@[category research solved, AMS 5 11 42]
theorem c3c_upper_bound_trivial : C3c ≤ 2 := by
  sorry

/-- Upper bound from [KT1999] (1999). -/
@[category research solved, AMS 5 11 42]
theorem c3c_upper_bound_kt1999 : C3c ≤ 2 - 1 / 4 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11 42]
theorem c3c_eq : answer(sorry) = C3c := by
  sorry

end Constant3c
