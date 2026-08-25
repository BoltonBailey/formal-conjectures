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
# Tao's Optimization constant 4a / The cap set constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 4a](https://teorth.github.io/optimizationproblems/constants/4a.html)
- [EG2016] Ellenberg, J. S.; Gijswijt, D. "On large subsets of $\mathbb{F}_q^n$ with no
  three-term arithmetic progression." Annals of Mathematics 185 (2017), 339–343.
  [arXiv:1605.09223](https://arxiv.org/abs/1605.09223)
- [E2004] Edel, Y. "Extensions of generalized product caps." Designs, Codes and Cryptography 31
  (2004), 5–14.
- [RBNBKDREWFKF2023] Romera-Paredes, B. et al. "Mathematical discoveries from program search
  with large language models." Nature 625 (2024), 468–475. FunSearch.
- [ZWLPLZJZZZ2025] X-evolve construction, 2025.
- [P1970] Pellegrino, Giuseppe. Sul massimo ordine delle calotte in $S_{4,3}$. Matematiche (Catania)
  25 (1970), no. 10, 1–9.
- [CF1994] Calderbank, A. Robert; Fishburn, Peter C. Maximal three-independent subsets of
  $\\{0,1,2\\}^n$. Des. Codes Cryptogr. 4, No. 3, 203-211 (1994).
- [T2023] Tyrrell, Fred. New lower bounds for cap sets. Discrete Analysis. 2023 (20).
  [arXiv:2209.10045](https://arxiv.org/abs/2209.10045).
-/

open Filter

namespace Constant4a

/-- The largest size of a cap set in $\mathbb{F}_3^n$, i.e. of a subset containing no line
(equivalently, no non-trivial three-term arithmetic progression). -/
noncomputable def capSetCard (n : ℕ) : ℕ :=
  Finset.maxAPFreeCard 3 (Finset.univ : Finset (𝔽₃ n))

/-- **Tao's Optimization constant 4a / The cap set constant**:
the growth rate $\lim_n r(n)^{1/n}$ of the largest cap set in $\mathbb{F}_3^n$. We take a
`limsup` so that the definition does not presuppose the existence of the limit. -/
@[optimization_constant "4a"]
noncomputable def C4a : ℝ := limsup (fun n : ℕ => (capSetCard n : ℝ) ^ ((n : ℝ)⁻¹)) atTop

/-- Trivial lower bound. -/
@[category research solved, AMS 5 11]
theorem c4a_lower_bound_trivial : 2 ≤ C4a := by
  classical
  have hkey : ∀ n : ℕ, (2 : ℕ) ^ n ≤ capSetCard n := by
    intro n
    set S : Finset (𝔽₃ n) := Fintype.piFinset (fun _ => ({0, 1} : Finset (ZMod 3))) with hSdef
    have hcard : S.card = 2 ^ n := by
      rw [hSdef, Fintype.card_piFinset]
      simp
    have hmemS : ∀ x : 𝔽₃ n, x ∈ S ↔ ∀ i, x i = 0 ∨ x i = 1 := by
      intro x
      rw [hSdef, Fintype.mem_piFinset]
      simp
    have hfree : (S : Set (𝔽₃ n)).IsAPOfLengthFree ((3 : ℕ) : ℕ∞) := by
      rintro t hts ⟨a, d, hcard3, hteq⟩
      exfalso
      have hmem : ∀ m : ℕ, (m : ℕ∞) < ((3 : ℕ) : ℕ∞) → a + m • d ∈ S := by
        intro m hm
        have hmS : a + m • d ∈ (S : Set (𝔽₃ n)) := hts (by rw [hteq]; exact ⟨m, hm, rfl⟩)
        exact_mod_cast hmS
      have h0 := (hmemS _).mp (hmem 0 (by norm_num))
      have h1 := (hmemS _).mp (hmem 1 (by norm_num))
      have h2 := (hmemS _).mp (hmem 2 (by norm_num))
      have hd : d = 0 := by
        funext i
        have e0 := h0 i
        have e1 := h1 i
        have e2 := h2 i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, zero_smul, add_zero,
          one_smul] at e0 e1 e2 ⊢
        revert e0 e1 e2
        generalize a i = x
        generalize d i = e
        revert x e
        decide
      subst hd
      have hts1 : t = {a} := by
        rw [hteq]
        ext x
        simp only [smul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        exact ⟨fun ⟨m, _, hm⟩ => hm.symm, fun h => ⟨0, by norm_num, h.symm⟩⟩
      rw [hts1] at hcard3
      simp at hcard3
    calc (2 : ℕ) ^ n = S.card := hcard.symm
      _ ≤ capSetCard n := by
          unfold capSetCard Finset.maxAPFreeCard
          refine Finset.le_sup (f := Finset.card) ?_
          simp only [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.subset_univ S, hfree⟩
  have hcardub : ∀ n : ℕ, capSetCard n ≤ 3 ^ n := by
    intro n
    unfold capSetCard Finset.maxAPFreeCard
    refine Finset.sup_le fun t ht => ?_
    calc t.card ≤ (Finset.univ : Finset (𝔽₃ n)).card := Finset.card_le_card (Finset.subset_univ t)
      _ = 3 ^ n := by simp
  refine le_limsup_of_frequently_le ((eventually_gt_atTop 0).frequently.mono fun n hn => ?_)
    (Filter.isBoundedUnder_of ⟨3, fun n => ?_⟩)
  · have h2 : ((2 : ℝ) ^ (n : ℕ)) ≤ (capSetCard n : ℝ) := by exact_mod_cast hkey n
    calc (2 : ℝ) = ((2 : ℝ) ^ (n : ℕ)) ^ ((n : ℝ)⁻¹) := by
          rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num),
            mul_inv_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
      _ ≤ (capSetCard n : ℝ) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h2 (by positivity)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have h2 : ((capSetCard n : ℝ)) ≤ (3 : ℝ) ^ (n : ℕ) := by exact_mod_cast hcardub n
      calc (capSetCard n : ℝ) ^ ((n : ℝ)⁻¹)
          ≤ ((3 : ℝ) ^ (n : ℕ)) ^ ((n : ℝ)⁻¹) :=
            Real.rpow_le_rpow (by positivity) h2 (by positivity)
        _ = 3 := by
            rw [← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_mul (by norm_num),
              mul_inv_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]

/-- Lower bound from [P1970] (1970). -/
@[category research solved, AMS 5 11]
theorem c4a_lower_bound_p1970 : 2.1146 ≤ C4a := by
  sorry

/-- Lower bound from [CF1994] (1994). -/
@[category research solved, AMS 5 11]
theorem c4a_lower_bound_cf1994 : 2.2101 ≤ C4a := by
  sorry

/-- Lower bound from [E2004] (2004). -/
@[category research solved, AMS 5 11]
theorem c4a_lower_bound_e2004 : 2.2173 ≤ C4a := by
  sorry

/-- Lower bound from [T2023] (2023). -/
@[category research solved, AMS 5 11]
theorem c4a_lower_bound_t2023 : 2.2180 ≤ C4a := by
  sorry

/-- Lower bound from [RBNBKDREWFKF2023] (2023). Funsearch -/
@[category research solved, AMS 5 11]
theorem c4a_lower_bound_rbnbkdrewfkf2023 : 2.2202 ≤ C4a := by
  sorry

/-- Lower bound from [ZWLPLZJZZZ2025] (2025). X-evolve -/
@[category research solved, AMS 5 11]
theorem c4a_lower_bound_zwlplzjzzz2025 : 2.2203 ≤ C4a := by
  sorry

/-- Trivial upper bound. -/
@[category research solved, AMS 5 11]
theorem c4a_upper_bound_trivial : C4a ≤ 3 := by
  have hcard : ∀ n : ℕ, capSetCard n ≤ 3 ^ n := by
    intro n
    unfold capSetCard Finset.maxAPFreeCard
    refine Finset.sup_le fun t ht => ?_
    calc t.card ≤ (Finset.univ : Finset (𝔽₃ n)).card := Finset.card_le_card (Finset.subset_univ t)
      _ = 3 ^ n := by simp
  refine limsup_le_of_le (Filter.isCoboundedUnder_le_of_le _
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h2 : ((capSetCard n : ℝ)) ≤ (3 : ℝ) ^ (n : ℕ) := by exact_mod_cast hcard n
  calc (capSetCard n : ℝ) ^ ((n : ℝ)⁻¹)
      ≤ ((3 : ℝ) ^ (n : ℕ)) ^ ((n : ℝ)⁻¹) := by
        apply Real.rpow_le_rpow (by positivity) h2 (by positivity)
    _ = 3 := by
        rw [← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_mul (by norm_num)]
        rw [mul_inv_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]

/-- Upper bound from [EG2016] (2017). -/
@[category research solved, AMS 5 11]
theorem c4a_upper_bound_eg2016 : C4a ≤ 2.756 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c4a_eq : answer(sorry) = C4a := by
  sorry

end Constant4a
