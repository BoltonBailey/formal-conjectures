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
# Tao's Optimization constant 4b / The Furstenberg-Sárközy exponent

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 4b](https://teorth.github.io/optimizationproblems/constants/4b.html)
- [Sar1978] Sárközy, A. "On difference sets of sequences of integers I." Acta Mathematica
  Academiae Scientiarum Hungaricae 31 (1978), 125–149.
- [Ruz1984] Ruzsa, I. Z. "Difference sets without squares." Periodica Mathematica Hungarica 15
  (1984), 205–209.
- [Lew2015] Lewko, M. "An improved lower bound related to the Furstenberg-Sárközy theorem."
  Electronic Journal of Combinatorics 22 (2015), P1.32.
- [BG2008] Beigel, R.; Gasarch, W. "Square-Difference-Free Sets of Size
  \(\Omega(n^{0.7334\ldots})\)." 2008. [arXiv:0804.4892](https://arxiv.org/abs/0804.4892)
-/

open Filter
open scoped Finset

namespace Constant4b

/-- The largest size of a subset of $\{1, \ldots, N\}$ with no non-zero square difference. -/
noncomputable def squareDifferenceFreeCard (N : ℕ) : ℕ :=
  sSup {#A | (A : Finset ℕ) (_ : A ⊆ Finset.Icc 1 N)
    (_ : ∀ a ∈ A, ∀ b ∈ A, ∀ n : ℕ, n ≠ 0 → a ≠ b + n ^ 2)}

/-- **Tao's Optimization constant 4b / The Furstenberg-Sárközy exponent**:
the least constant $c$ with $r(N) \le N^{c + o(1)}$, where $r(N)$ is the largest size of a
square-difference-free subset of $\{1, \ldots, N\}$. We take a `limsup`, since the existence of
the limit is itself open [Ruz1984]. -/
@[optimization_constant "4b"]
noncomputable def C4b : ℝ :=
  limsup (fun N : ℕ => Real.log (squareDifferenceFreeCard N) / Real.log N) atTop

/-- Lower bound from Trivial / folklore (see [BG2008]) (2008). Can use an arithmetic progression of
spacing $p \asymp \sqrt{N}$ -/
@[category research solved, AMS 5 11]
theorem c4b_lower_bound_bg2008 : 1 / 2 ≤ C4b := by
  sorry

/-- Lower bound from [Ruz1984] (1984). Base-expansion construction -/
@[category research solved, AMS 5 11]
theorem c4b_lower_bound_ruz1984 : 1 / 2 * (1 + Real.log 7 / Real.log 65) ≤ C4b := by
  sorry

/-- Lower bound from [Lew2015] (2015). Improves modulus and residue set in base expansion -/
@[category research solved, AMS 5 11]
theorem c4b_lower_bound_lew2015 : 1 / 2 * (1 + Real.log 12 / Real.log 205) ≤ C4b := by
  sorry

/-- Trivial upper bound. -/
@[category research solved, AMS 5 11]
theorem c4b_upper_bound_trivial : C4b ≤ 1 := by
  have hlog : ∀ m : ℕ, 0 ≤ Real.log m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hm)
  have hcard : ∀ N : ℕ, squareDifferenceFreeCard N ≤ N := by
    intro N
    refine csSup_le ⟨0, ∅, by simp, by simp, rfl⟩ ?_
    rintro x ⟨A, hA, -, rfl⟩
    calc #A ≤ #(Finset.Icc 1 N) := Finset.card_le_card hA
      _ = N := by simp
  refine limsup_le_of_le (Filter.isCoboundedUnder_le_of_le _
    (fun n => div_nonneg (hlog _) (hlog _))) ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  rw [div_le_one hlogN]
  rcases Nat.eq_zero_or_pos (squareDifferenceFreeCard N) with h0 | h0
  · rw [h0]; simpa using hlogN.le
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard N)

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c4b_eq : answer(sorry) = C4b := by
  sorry

end Constant4b
