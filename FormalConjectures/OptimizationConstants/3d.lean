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
# Tao's Optimization constant 3d / The single-set sum-difference exponent

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 3d](https://teorth.github.io/optimizationproblems/constants/3d.html)
- [Ru96] Ruzsa, I. Z. "Sums of finite sets." Number Theory (New York, 1991–1995), Springer
  (1996), 281–293.
- [PeWe13] Penman, D.; Wells, M. "On sets with more restricted sums than differences."
  Integers 13 (2013), A57.
- [LiLi26] Solution of the problem, establishing that the exponent equals $2$, 2026.
- [FrPi73] Freiman, G. A.; Pigaev, V. P. "The relation between the invariants $r$ and $t$." Kalinin.
  Gos. Univ., Moscow, 1973, pp. 172–174.
- [GGSWT2025] Georgiev, Bogdan; Gómez-Serrano, Javier; Tao, Terence; Wagner, Adam Zsolt.
  "Mathematical exploration and discovery at scale."
  [arXiv:2511.02864](https://arxiv.org/abs/2511.02864)
-/

open scoped Pointwise Finset

namespace Constant3d

/-- The doubling constant $\sigma(A) = |A + A| / |A|$ of a finite set. -/
noncomputable def σ (A : Finset ℤ) : ℝ := (#(A + A) : ℝ) / #A

/-- The difference constant $\delta(A) = |A - A| / |A|$ of a finite set. -/
noncomputable def δ (A : Finset ℤ) : ℝ := (#(A - A) : ℝ) / #A

/-- **Tao's Optimization constant 3d / The single-set sum-difference exponent**:
the supremum of $\log \sigma(A) / \log \delta(A)$ over finite sets $A$ of integers with
$|A| \ge 2$ and $\delta(A) > 1$; equivalently the least $\theta$ with
$\sigma(A) \le \delta(A)^\theta$ for every finite $A$. -/
@[optimization_constant "3d"]
noncomputable def C3d : ℝ :=
  sSup {t : ℝ | ∃ A : Finset ℤ, 2 ≤ #A ∧ 1 < δ A ∧ t = Real.log (σ A) / Real.log (δ A)}

/-- Lower bound from [FrPi73] (1973). From the $17$-element set $A =
\{0,1,2,4,5,9,12,13,14,16,17,21,24,25,26,28,29\}$, which has $\lvert A+A\rvert = 59$ and $\lvert
A-A\rvert = 55$ [GGSWT2025, Problem 6.42]. Used as the baseline in [GGSWT2025] and quoted as such by
[LiLi26]. -/
@[category research solved, AMS 5 11]
theorem c3d_lower_bound_frpi73 : Real.log (59 / 17) / Real.log (55 / 17) ≤ C3d := by
  sorry

/-- Lower bound from [PeWe13] (2013). Theorem 21 of [PeWe13]: the supremum of $C(Q\_j)$ over their
family $Q\_j$, approached as $j \to \infty$ but not attained. From their Corollary 13, $\lvert
Q\_j\rvert = 5j+17$, $\lvert Q\_j+Q\_j\rvert = 32j+63$ and $\lvert Q\_j-Q\_j\rvert = 26j+61$, whence
$\sigma \to 32/5$ and $\delta \to 26/5$. This held the record until [LiLi26]. -/
@[category research solved, AMS 5 11]
theorem c3d_lower_bound_pewe13 : Real.log (32 / 5) / Real.log (26 / 5) ≤ C3d := by
  sorry

/-- Lower bound from [GGSWT2025] (2025). The website lists this value as approximate ($\approx
1.1219$). This constant is **Problem 6.42** of [GGSWT2025], where AlphaEvolve found $A = A\_1 \cup
A\_2$ with $A\_1 = \{-159,-158,\dots,111\}$ and $A\_2$ an explicit $38$-element set, with no human
hints. Inferior to the Penman–Wells record. -/
@[category research solved, AMS 5 11]
theorem c3d_lower_bound_ggswt2025 : 1.1219 ≤ C3d := by
  sorry

/-- Lower bound from [LiLi26] (2026). Solves the problem: $C\_{3d} = 2$. Explicit family with
$\sigma \gg K$ and $\delta \ll K^{1/2}$ for arbitrarily large $K$; [LiLi26] states it as $C(A\_K) >
\frac{2K}{K+3}$ for every positive even $K$. -/
@[category research solved, AMS 5 11]
theorem c3d_lower_bound_lili26 : 2 ≤ C3d := by
  sorry

/-- Upper bound from [Ru96] (1996). $\sigma \le \delta^2$. Attributed to [Ru96, Theorem 4.1] in
[GGSWT2025, Problem 6.42]; [Bl26] describes it as a consequence of the Plünnecke–Ruzsa inequalities.
-/
@[category research solved, AMS 5 11]
theorem c3d_upper_bound_ru96 : C3d ≤ 2 := by
  refine Real.sSup_le ?_ (by norm_num)
  rintro t ⟨A, hA2, hδ, rfl⟩
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hApos : (0 : ℝ) < (#A : ℝ) := by
    have h : 0 < #A := by omega
    exact_mod_cast h
  have hδpos : 0 < Real.log (δ A) := Real.log_pos hδ
  have hpr := Finset.pluennecke_ruzsa_inequality_nsmul_sub hAne A 2
  rw [two_nsmul] at hpr
  have hpr' : ((#(A + A) : ℝ)) ≤ ((#(A - A) : ℝ) / (#A : ℝ)) ^ 2 * (#A : ℝ) := by
    have hc := (NNRat.cast_le (K := ℝ)).mpr hpr
    push_cast at hc
    exact hc
  have hσδ : σ A ≤ δ A ^ 2 := by
    rw [σ, δ, div_le_iff₀ hApos] at *
    nlinarith [hpr']
  have hσ1 : 1 ≤ σ A := by
    rw [σ, le_div_iff₀ hApos, one_mul]
    exact_mod_cast Finset.card_le_card_add_left hAne
  rw [div_le_iff₀ hδpos]
  calc Real.log (σ A) ≤ Real.log (δ A ^ 2) := Real.log_le_log (by linarith) hσδ
    _ = 2 * Real.log (δ A) := by rw [Real.log_pow]; push_cast; ring

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c3d_eq : answer(sorry) = C3d := by
  sorry

end Constant3d
