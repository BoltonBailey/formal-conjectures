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
import FormalConjectures.ErdosProblems.«519»

/-!
# Tao's Optimization constant 42a / Turán's pure power sum constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 42a](https://teorth.github.io/optimizationproblems/constants/42a.html)
- [Atk61] Atkinson, F. V. "On sums of powers of complex numbers." Acta Math. Acad. Sci. Hungar. 12
  (1961), 185–188.
- [Bir94] Biró, A. "On a problem of Turán concerning sums of powers of complex numbers." Acta
  Math. Hungar. 65 (1994), 209–216.
- [Bir00] Biró, A. "An upper estimate in Turán's pure power sum problem." Acta Math. Hungar. 86
  (2000), 231–238.
- [Atk69] Atkinson, F. V. "Some further estimates concerning sums of powers of complex numbers."
  Acta Math. Acad. Sci. Hungar. 20 (1969), 193-210.
- [Bir00b] Biró, A. "An improved estimate in a power sum problem of Tur\'{a}n." Indag. Math. (N.S.)
  11 (2000), no. 3, 343-358.
- [Gri26] Griego, S. "An improved asymptotic certificate for Turan's pure power sum constant
  $C_{42}$." GitHub repository, version `v1.0.0`, commit `c8ddce14d9a5e898406d5dc6b8d08bb8a39507c7`
  (2026). https://github.com/sebastian-griego/turan-c42-certificate/tree/v1.0.0

The power sums are formalised in `FormalConjectures.ErdosProblems.«519»` as `Erdos519.powerSum`.
-/

open Filter

namespace Constant42a

/-- The quantity $R_n$: the minimum over $z_1, \ldots, z_n \in \mathbb{C}$ with
$\max_i |z_i| = 1$ of $\max_{1 \le k \le n} \left| \sum_i z_i^k \right|$. -/
noncomputable def R (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ z : Fin n → ℂ, (⨆ i, ‖z i‖) = 1 ∧
    r = ⨆ k : Fin n, ‖Erdos519.powerSum z (k.val + 1)‖}

/-- **Tao's Optimization constant 42a / Turán's pure power sum constant**:
$\limsup_{n \to \infty} R_n$, where $R_n$ is the minimum over unit-normalised
$z_1, \ldots, z_n \in \mathbb{C}$ of $\max_{1 \le k \le n} \left| \sum_i z_i^k \right|$. -/
@[optimization_constant "42a"]
noncomputable def C42a : ℝ := limsup R atTop

/-- Lower bound from Atkinson [Atk61] (1961). -/
@[category research solved, AMS 11 30]
theorem c42a_lower_bound_atk61 : 1 / 6 ≤ C42a := by
  sorry

/-- Lower bound from Atkinson. Mentioned in [Atk69] in a (presumably unpublished) technical report.
-/
@[category research solved, AMS 11 30]
theorem c42a_lower_bound_atkinson : 1 / 3 ≤ C42a := by
  sorry

/-- Lower bound from Atkinson [Atk69] (1969). -/
@[category research solved, AMS 11 30]
theorem c42a_lower_bound_atk69 : Real.pi / 8 ≤ C42a := by
  sorry

/-- Lower bound from Biró [Bir94] (2000). -/
@[category research solved, AMS 11 30]
theorem c42a_lower_bound_bir94 : 1 / 2 ≤ C42a := by
  sorry

/-- Lower bound from Biró [Bir00b] (2000). Biró's proof delivers some computable constant
$1/2<c<1/\sqrt{2}$, but it is not computed there exactly which. -/
@[category research solved, AMS 11 30]
theorem c42a_lower_bound_bir00b : 1 / 2 < C42a := by
  sorry

/-- Trivial upper bound. -/
@[category research solved, AMS 11 30]
theorem c42a_upper_bound_trivial : C42a ≤ 1 := by
  have hnn : ∀ (n : ℕ) (r : ℝ), r ∈ {r : ℝ | ∃ z : Fin n → ℂ, (⨆ i, ‖z i‖) = 1 ∧
      r = ⨆ k : Fin n, ‖Erdos519.powerSum z (k.val + 1)‖} → 0 ≤ r := by
    rintro n r ⟨w, -, rfl⟩
    exact Real.iSup_nonneg fun k => norm_nonneg _
  have hRnn : ∀ n : ℕ, 0 ≤ R n := fun n => Real.sInf_nonneg (hnn n)
  have hR1 : ∀ n : ℕ, 0 < n → R n ≤ 1 := by
    intro n hn
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    set z : Fin n → ℂ := fun i => if i = ⟨0, hn⟩ then 1 else 0 with hz
    have hsup : (⨆ i, ‖z i‖) = 1 := by
      refine le_antisymm (ciSup_le fun i => ?_) ?_
      · by_cases h : i = ⟨0, hn⟩ <;> simp [hz, h]
      · refine le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _)) ⟨0, hn⟩ ?_
        simp [hz]
    have hps : ∀ m : ℕ, Erdos519.powerSum z (m + 1) = 1 := by
      intro m
      have hpt : ∀ i : Fin n, z i ^ (m + 1) = if i = ⟨0, hn⟩ then (1 : ℂ) else 0 := by
        intro i
        by_cases h : i = ⟨0, hn⟩ <;> simp [hz, h]
      simp [Erdos519.powerSum, hpt]
    have hval : (⨆ k : Fin n, ‖Erdos519.powerSum z (k.val + 1)‖) = 1 := by
      simp [hps]
    refine csInf_le ⟨0, fun r hr => hnn n r hr⟩ ⟨z, hsup, hval.symm⟩
  refine limsup_le_of_le (Filter.isCoboundedUnder_le_of_le _ hRnn) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn using hR1 n hn

/-- Upper bound from Biró [Bir00] (2000). -/
@[category research solved, AMS 11 30]
theorem c42a_upper_bound_bir00_1 : C42a ≤ 5 / 6 := by
  sorry

/-- Upper bound from Harcos [Bir00] (2000). -/
@[category research solved, AMS 11 30]
theorem c42a_upper_bound_bir00_2 : C42a ≤ 0.69368 := by
  sorry

/-- Upper bound from Griego [Gri26] (2026). Proposed asymptotic two-block certificate with exact
rational interval verification of the limiting inequality. No explicit finite threshold $N$ is
supplied. -/
@[category research solved, AMS 11 30]
theorem c42a_upper_bound_gri26 : C42a ≤ 0.6906538 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11 30]
theorem c42a_eq : answer(sorry) = C42a := by
  sorry

end Constant42a
