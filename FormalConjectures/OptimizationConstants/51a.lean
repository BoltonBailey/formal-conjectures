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
import FormalConjectures.ErdosProblems.«513»

/-!
# Tao's Optimization constant 51a / The Erdős maximum-term constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 51a](https://teorth.github.io/optimizationproblems/constants/51a.html)
- [Er1961] Erdős, P. "Some unsolved problems." Magyar Tud. Akad. Mat. Kutató Int. Közl. 6 (1961),
  221–254.
- [CH1964] Clunie, J.; Hayman, W. K. "The maximum term of a power series." Journal d'Analyse
  Mathématique 12 (1964), 143–186.
- [HT2026] Hunter, Z.; Tao, T. "Improved bounds for the maximum term problem." 2026.
- [S2026] Sothanaphan, Nat. "A certified computation for an improved He–Tang parameter choice in
  Erdős’ maximum-term problem." 2026.
  https://drive.google.com/file/d/1wZnzui_eeBE32HnkrnSB7YhfcTOiYolp/view

The underlying ratio is formalised in `FormalConjectures.ErdosProblems.«513»` as `Erdos513.ratio`.
-/

open Filter Polynomial
open scoped Real

namespace Constant51a

/-- **Tao's Optimization constant 51a / The Erdős maximum-term constant**:
the supremum over transcendental entire functions $f$ of
$\liminf_{r \to \infty} \frac{\mu(r, f)}{M(r, f)}$, where $\mu(r, f)$ is the maximum term of the
power series of $f$ and $M(r, f)$ is the maximum modulus of $f$ on the circle of radius $r$. -/
@[optimization_constant "51a"]
noncomputable def C51a : ℝ :=
  ⨆ f : {f : ℂ → ℂ // Transcendental ℂ[X] f ∧ Differentiable ℂ f},
    liminf (fun r : ℝ => Erdos513.ratio r f) atTop

/-- Lower bound from [Er1961] (1961). -/
@[category research solved, AMS 30]
theorem c51a_lower_bound_er1961 : 1 / 2 ≤ C51a := by
  sorry

/-- Lower bound from Kövári (unpublished). Cited in [HT2026] -/
@[category research solved, AMS 30]
theorem c51a_lower_bound_kovari : 1 / 2 < C51a := by
  sorry

/-- Lower bound from [CH1964] (1964). Scaling-identity construction. -/
@[category research solved, AMS 30]
theorem c51a_lower_bound_ch1964 : 4 / 7 ≤ C51a := by
  sorry

/-- Lower bound from [HT2026] (2026). Certified (computer-assisted) improvement using a
two-parameter generalization of the Clunie–Hayman construction. -/
@[category research solved, AMS 30]
theorem c51a_lower_bound_ht2026 : 0.5850724 ≤ C51a := by
  sorry

/-- Lower bound from [S2026] (2026). Used GPT 5.2. Discussed
[here](https://www.erdosproblems.com/forum/thread/513#post-4532) -/
@[category research solved, AMS 30]
theorem c51a_lower_bound_s2026 : 0.5850788 ≤ C51a := by
  sorry

/-- Trivial upper bound. Follows from Cauchy estimates -/
@[category research solved, AMS 30]
theorem c51a_upper_bound_trivial : C51a ≤ 1 := by
  refine Real.iSup_le (fun F => ?_) zero_le_one
  obtain ⟨f, -, hdiff⟩ := F
  refine liminf_le_of_frequently_le
    ((eventually_ge_atTop (1 : ℝ)).frequently.mono fun r hr => ?_)
    (Filter.isBoundedUnder_of ⟨0, fun r => div_nonneg (Real.iSup_nonneg fun n => norm_nonneg _)
      (Real.iSup_nonneg fun z => norm_nonneg _)⟩)
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hDnn : (0 : ℝ) ≤ ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖ :=
    Real.iSup_nonneg fun z => norm_nonneg _
  rw [Erdos513.ratio]
  rcases eq_or_lt_of_le hDnn with hD0 | hDpos
  · rw [← hD0, div_zero]; norm_num
  · rw [div_le_one hDpos]
    have hbdd : BddAbove (Set.range fun z : {z : ℂ // ‖z‖ = r} => ‖f z‖) := by
      have hc : IsCompact (Metric.sphere (0 : ℂ) r) := isCompact_sphere 0 r
      have heq : (Set.range fun z : {z : ℂ // ‖z‖ = r} => ‖f z‖)
          = (fun z => ‖f z‖) '' (Metric.sphere (0 : ℂ) r) := by
        ext y
        constructor
        · rintro ⟨⟨z, hz⟩, rfl⟩
          exact ⟨z, by simpa [Complex.norm_def] using hz, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          exact ⟨⟨z, by simpa using hz⟩, rfl⟩
      rw [heq]
      exact (hc.image (continuous_norm.comp hdiff.continuous)).bddAbove
    have hsph : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖ :=
      fun z hz => le_ciSup hbdd ⟨z, by simpa using hz⟩
    refine ciSup_le fun n => ?_
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr0
      (hdiff.diffContOnCl (s := Metric.ball 0 r)) hsph
    have hfact : (0 : ℝ) < (n.factorial : ℝ) := by positivity
    have hrn : (0 : ℝ) < r ^ n := by positivity
    rw [le_div_iff₀ hrn] at hcauchy
    rw [norm_mul, norm_mul]
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_inv, abs_of_pos hr0,
      abs_of_pos hfact]
    rw [show ‖iteratedDeriv n f 0‖ * ((n.factorial : ℝ))⁻¹ * r ^ n
        = (‖iteratedDeriv n f 0‖ * r ^ n) / (n.factorial : ℝ) from by ring,
      div_le_iff₀ hfact]
    calc ‖iteratedDeriv n f 0‖ * r ^ n
        ≤ (n.factorial : ℝ) * (⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖) := hcauchy
      _ = (⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖) * (n.factorial : ℝ) := mul_comm _ _

/-- Upper bound from [CH1964] (1964). -/
@[category research solved, AMS 30]
theorem c51a_upper_bound_ch1964 : C51a ≤ 2 / Real.pi := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 30]
theorem c51a_eq : answer(sorry) = C51a := by
  sorry

end Constant51a
