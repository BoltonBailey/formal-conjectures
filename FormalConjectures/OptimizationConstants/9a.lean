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
import FormalConjectures.GreensOpenProblems.«38»

/-!
# Tao's Optimization constant 9a / The Shannon capacity of the 7-cycle

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 9a](https://teorth.github.io/optimizationproblems/constants/9a.html)
- [S1956] Shannon, C. E. "The zero error capacity of a noisy channel." IRE Transactions on
  Information Theory 2 (1956), 8–19.
- [L1979] Lovász, L. "On the Shannon capacity of a graph." IEEE Transactions on Information
  Theory 25 (1979), 1–7.
- [PS2018] Polak, S. C.; Schrijver, A. "New lower bound on the Shannon capacity of $C_7$ from
  circular graphs." Information Processing Letters 143 (2019), 37–40.
  [arXiv:1808.07438](https://arxiv.org/abs/1808.07438)
- [BMRRST1971] L. Baumert, R. McEliece, E. Rodemich, H. Rumsey, R. Stanley, H. Taylor. A
  combinatorial packing problem. Computers in Algebra and Number Theory, American Mathematical
  Society, Providence, RI (1971), 97–108.
- [VZ2002] A. Vesel, J. Zerovnik. Improved lower bound on the Shannon capacity of $C\_7$.
  Information Processing Letters, 81 (2002), 277–282.
- [MO2017] K.A. Mathew, P.R.J. Östergård. New lower bounds for the Shannon capacity of odd cycles.
  Designs, Codes and Cryptography, 84 (2017), 13–22.

The independence numbers $\alpha(C_7^{\boxtimes n})$ are formalised in
`FormalConjectures.GreensOpenProblems.«38»` as `Green38.LargestAdmissibleCardinality`: a subset
$A \subseteq \mathbb{F}_7^n$ with $(A - A) \cap \{-1, 0, 1\}^n = \{0\}$ is exactly an independent
set in the $n$-th strong power of $C_7$.
-/

namespace Constant9a

/-- **Tao's Optimization constant 9a / The Shannon capacity of the 7-cycle**:
$\Theta(C_7) = \sup_{n \ge 1} \alpha(C_7^{\boxtimes n})^{1/n}$, where $\alpha$ denotes the
independence number and $\boxtimes$ the strong graph product. -/
@[optimization_constant "9a"]
noncomputable def C9a : ℝ :=
  ⨆ n : ℕ, Green38.LargestAdmissibleCardinality (n + 1) ^ (((n : ℝ) + 1)⁻¹)

/-- Trivial lower bound. -/
@[category research solved, AMS 5 94]
theorem c9a_lower_bound_trivial : 3 ≤ C9a := by
  have hLACnn : ∀ m : ℕ, (0 : ℝ) ≤ Green38.LargestAdmissibleCardinality m := fun m =>
    Nat.cast_nonneg _
  have hLAC : ∀ m : ℕ, Green38.LargestAdmissibleCardinality m ≤ (7 : ℝ) ^ m := by
    intro m
    have h : sSup (Green38.ValidCardinalities m) ≤ 7 ^ m := by
      refine csSup_le ⟨0, Green38.green_38.test_zero_mem_validCardinalities⟩ ?_
      rintro b ⟨A, -, rfl⟩
      calc A.card ≤ Fintype.card (𝔽₇ m) := Finset.card_le_univ A
        _ = 7 ^ m := by simp
    calc Green38.LargestAdmissibleCardinality m
        = ((sSup (Green38.ValidCardinalities m) : ℕ) : ℝ) := rfl
      _ ≤ ((7 ^ m : ℕ) : ℝ) := by exact_mod_cast h
      _ = (7 : ℝ) ^ m := by push_cast; ring
  have hbdd : BddAbove (Set.range fun n : ℕ =>
      Green38.LargestAdmissibleCardinality (n + 1) ^ (((n : ℝ) + 1)⁻¹)) := by
    refine ⟨7, ?_⟩
    rintro x ⟨n, rfl⟩
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc Green38.LargestAdmissibleCardinality (n + 1) ^ (((n : ℝ) + 1)⁻¹)
        ≤ ((7 : ℝ) ^ (n + 1)) ^ (((n : ℝ) + 1)⁻¹) :=
          Real.rpow_le_rpow (hLACnn _) (hLAC (n + 1)) (by positivity)
      _ = 7 := by
          rw [← Real.rpow_natCast (7 : ℝ) (n + 1), ← Real.rpow_mul (by norm_num)]
          push_cast
          rw [mul_inv_cancel₀ hpos.ne', Real.rpow_one]
  refine le_ciSup_of_le hbdd 0 ?_
  simp only [Nat.cast_zero, zero_add, inv_one, Real.rpow_one]
  have h3 : (3 : ℕ) ≤ sSup (Green38.ValidCardinalities 1) :=
    le_csSup Green38.green_38.test_bound_above Green38.green_38.test_n1_lower
  calc (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    _ ≤ ((sSup (Green38.ValidCardinalities 1) : ℕ) : ℝ) := by exact_mod_cast h3
    _ = Green38.LargestAdmissibleCardinality 1 := rfl

/-- Lower bound from [BMRRST1971] (1971). -/
@[category research solved, AMS 5 94]
theorem c9a_lower_bound_bmrrst1971 : 343 ^ (1 / 5 : ℝ) ≤ C9a := by
  sorry

/-- Lower bound from [VZ2002] (2002). -/
@[category research solved, AMS 5 94]
theorem c9a_lower_bound_vz2002 : 108 ^ (1 / 4 : ℝ) ≤ C9a := by
  sorry

/-- Lower bound from [MO2017] (2017). -/
@[category research solved, AMS 5 94]
theorem c9a_lower_bound_mo2017 : 350 ^ (1 / 5 : ℝ) ≤ C9a := by
  sorry

/-- Lower bound from [PS2018] (1808). -/
@[category research solved, AMS 5 94]
theorem c9a_lower_bound_ps2018 : 367 ^ (1 / 5 : ℝ) ≤ C9a := by
  sorry

/-- Upper bound from [S1956] (1956). Fractional clique cover bound -/
@[category research solved, AMS 5 94]
theorem c9a_upper_bound_s1956 : C9a ≤ 7 / 2 := by
  sorry

/-- Upper bound from [L1979] (1979). The Lovász theta number $\vartheta(C_7) = \frac{7\cos(\pi/7)}{1
+ \cos(\pi/7)} \approx 3.3177$. Lovász theta-function bound -/
@[category research solved, AMS 5 94]
theorem c9a_upper_bound_l1979 :
    C9a ≤ 7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7)) := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 94]
theorem c9a_eq : answer(sorry) = C9a := by
  sorry

end Constant9a
