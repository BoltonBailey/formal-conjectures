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
- [GGSWT2025] Georgiev, Bogdan; Gómez-Serrano, Javier; Tao, Terence; Wagner, Adam Zsolt.
  Mathematical exploration and discovery at scale.
  [arXiv:2511.02864](https://arxiv.org/abs/2511.02864)
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

/-- Trivial lower bound. -/
@[category research solved, AMS 5 11 42]
theorem c3b_lower_bound_trivial : Real.log 3 / Real.log 2 ≤ C3b := by
  sorry

/-- Lower bound from Ruzsa (unpublished). -/
@[category research solved, AMS 5 11 42]
theorem c3b_lower_bound_ruzsa : Real.log 27 / Real.log (27 / 4) ≤ C3b := by
  sorry

/-- Lower bound from [L2015] (2015). -/
@[category research solved, AMS 5 11 42]
theorem c3b_lower_bound_l2015 : 1.77898 ≤ C3b := by
  sorry

/-- Lower bound from [GGSWT2025] (2025). Improved [L2015] in the eighth decimal place (AlphaEvolve)
-/
@[category research solved, AMS 5 11 42]
theorem c3b_lower_bound_ggswt2025 : 1.77898 < C3b := by
  sorry

/-- Lower bound from [MI2026] (2026). Entropy construction on a 13-point support. -/
@[category research solved, AMS 5 11 42]
theorem c3b_lower_bound_mi2026 : 1.77898884 ≤ C3b := by
  sorry

/-- Trivial upper bound. -/
@[category research solved, AMS 5 11 42]
theorem c3b_upper_bound_trivial : C3b ≤ 2 := by
  have key : ∀ (S : Set ℝ) (a : ℝ), 0 ≤ a → a ∈ S → sInf S ≤ a := by
    intro S a ha haS
    by_cases h : BddBelow S
    · exact csInf_le h haS
    · rw [Real.sInf_of_not_bddBelow h]; exact ha
  refine key _ 2 (by norm_num) ?_
  intro A B G hG
  set M := max (max (#A : ℝ) (#B : ℝ)) (#(G.image fun p => p.1 + p.2) : ℝ) with hM
  have hA : (#A : ℝ) ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hB : (#B : ℝ) ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hA0 : (0 : ℝ) ≤ (#A : ℝ) := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (#B : ℝ) := Nat.cast_nonneg _
  have h1 : (#(G.image fun p => p.1 - p.2) : ℝ) ≤ (#G : ℝ) := by
    exact_mod_cast Finset.card_image_le
  have h2 : (#G : ℝ) ≤ (#A : ℝ) * (#B : ℝ) := by
    have h := Finset.card_le_card hG
    rw [Finset.card_product] at h
    exact_mod_cast h
  have h3 : (#A : ℝ) * (#B : ℝ) ≤ M ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq]
    exact mul_le_mul hA hB hB0 (hA0.trans hA)
  linarith

/-- Upper bound from Wolff (unpublished). -/
@[category research solved, AMS 5 11 42]
theorem c3b_upper_bound_wolff : C3b ≤ 2 - 1 / 14 := by
  sorry

/-- Upper bound from [B1999] (1999). -/
@[category research solved, AMS 5 11 42]
theorem c3b_upper_bound_b1999 : C3b ≤ 2 - 1 / 13 := by
  sorry

/-- Upper bound from [KT1999] (1999). -/
@[category research solved, AMS 5 11 42]
theorem c3b_upper_bound_kt1999 : C3b ≤ 2 - 1 / 6 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11 42]
theorem c3b_eq : answer(sorry) = C3b := by
  sorry

end Constant3b
