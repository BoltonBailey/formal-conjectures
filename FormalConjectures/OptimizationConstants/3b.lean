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
# Tao's Optimization constant 3b / The Kakeya-type sum-difference constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 3b](https://teorth.github.io/optimizationproblems/constants/3b.html)
- [B1999] Bourgain, J. "On the dimension of Kakeya sets and related maximal inequalities."
  Geometric and Functional Analysis 9 (1999), 256–282.
- [KT1999] Katz, N. H.; Tao, T. "Bounds on arithmetic projections, and applications to the
  Kakeya conjecture." Mathematical Research Letters 6 (1999), 625–630.
- [L2015] Łaba, I. Lower bound construction, 2015.
- [MI2026] Entropy construction on a 13-point support, 2026.
-/

open scoped Pointwise Finset

namespace Constant3b

/-- **Tao's Optimization constant 3b / The Kakeya-type sum-difference constant**:
the least exponent $c$ such that
$|A \stackrel{G}{-} B| \le \max(|A|, |B|, |A \stackrel{G}{+} B|)^c$ for all finite
$A, B \subseteq \mathbb{R}$ and all $G \subseteq A \times B$, where
$A \stackrel{G}{\pm} B := \{a \pm b : (a, b) \in G\}$. -/
@[optimization_constant "3b"]
noncomputable def C3b : ℝ :=
  sInf {c : ℝ | ∀ (A B : Finset ℝ) (G : Finset (ℝ × ℝ)), G ⊆ A ×ˢ B →
    (#(G.image fun p => p.1 - p.2) : ℝ) ≤
      max (max (#A : ℝ) (#B : ℝ)) (#(G.image fun p => p.1 + p.2) : ℝ) ^ c}

/-- The best known lower bound $1.77898884$, given by an entropy construction on a $13$-point
support [MI2026], refining the bound $1.77898$ of [L2015]. -/
@[category research solved, AMS 5 11 42]
theorem c3b_lower_bound : 1.77898884 ≤ C3b := by
  sorry

/-- The best known upper bound $2 - 1/6 = 11/6$, proven by Katz-Tao in [KT1999]. -/
@[category research solved, AMS 5 11 42]
theorem c3b_upper_bound : C3b ≤ 11 / 6 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 5 11 42]
theorem mem_Ico_c3b : answer(sorry) ∈ Set.Ico C3b (11 / 6) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5 11 42]
theorem mem_Ioc_c3b : answer(sorry) ∈ Set.Ioc 1.77898884 C3b := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11 42]
theorem c3b_eq : C3b = answer(sorry) := by
  sorry

end Constant3b
