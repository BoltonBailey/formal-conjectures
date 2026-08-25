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
import FormalConjectures.Wikipedia.UnionClosed

/-!
# Tao's Optimization constant 6a / The union-closed sets constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 6a](https://teorth.github.io/optimizationproblems/constants/6a.html)
- [F1995] Frankl, P. "Extremal set systems." Handbook of Combinatorics, Vol. 2 (1995),
  1293–1329. The conjecture that the constant equals $1/2$ is due to Frankl (1976).
- [G2022] Gilmer, J. "A constant lower bound for the union-closed sets conjecture."
  [arXiv:2211.09055](https://arxiv.org/abs/2211.09055)
- [L2023] Liu, L. "Improved bounds for the union-closed sets conjecture."
  [arXiv:2311.05737](https://arxiv.org/abs/2311.05737)
- [AHS2022] Alweiss, Ryan; Huang, Brice; Sellke, Mark. Improved lower bound for the union-closed
  sets conjecture. arXiv preprint arXiv:2211.11731, 2022.
- [CL2022] Chase, Zachary; Lovett, Shachar. Approximate union closed conjecture. arXiv preprint
  arXiv:2211.11689, 2022.
- [P2022] Pebody, Luke. Extension of a method of Gilmer. arXiv preprint arXiv:2211.13139, 2022.
- [S2022] Sawin, Will. An improved lower bound for the union-closed set conjecture. arXiv preprint
  arXiv:2211.11504, 2022.
- [C2022] Cambie, Stijn. Better bounds for the union-closed sets conjecture using the entropy
  approach. arXiv preprint arXiv:2212.12500, 2022.
- [Y2022] Yu, Lei. Dimension-Free Bounds for the Union-Closed Sets Conjecture. arXiv preprint
  arXiv:2212.00658, 2022.

The union-closed condition is formalised in `FormalConjectures.Wikipedia.UnionClosed` as
`UnionClosed.IsUnionClosed`.
-/

open Finset

namespace Constant6a

/-- **Tao's Optimization constant 6a / The union-closed sets constant**:
the largest constant $C$ such that every union-closed family of sets, other than the family
containing only the empty set, has an element belonging to at least a $C$ fraction of the sets. -/
@[optimization_constant "6a"]
noncomputable def C6a : ℝ :=
  sSup {c : ℝ | ∀ (n : ℕ) (A : Finset (Finset (Fin n))), A.Nonempty → A ≠ {∅} →
    UnionClosed.IsUnionClosed A → ∃ i : Fin n, c * #A ≤ #{x ∈ A | i ∈ x}}

/-- Trivial lower bound. -/
@[category research solved, AMS 5]
theorem c6a_lower_bound_trivial : 0 ≤ C6a := by
  refine Real.sSup_nonneg' ⟨0, ?_, le_rfl⟩
  intro n A hA hA' _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd (Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨hA, fun x _ => Finset.eq_empty_of_isEmpty x⟩) hA'
  · exact ⟨⟨0, hn⟩, by simp⟩

/-- Lower bound from [G2022] (2022). -/
@[category research solved, AMS 5]
theorem c6a_lower_bound_g2022 : 0.1 ≤ C6a := by
  sorry

/-- Lower bound from [AHS2022], [CL2022], [P2022], [S2022] (2022). -/
@[category research solved, AMS 5]
theorem c6a_lower_bound_ahs2022_cl2022_p2022_s2022 : (3 - Real.sqrt 5) / 2 ≤ C6a := by
  sorry

/-- Lower bound from [S2022] (2022). -/
@[category research solved, AMS 5]
theorem c6a_lower_bound_s2022 : (3 - Real.sqrt 5) / 2 < C6a := by
  sorry

/-- Lower bound from [C2022], [Y2022] (2022). -/
@[category research solved, AMS 5]
theorem c6a_lower_bound_c2022_y2022 : 0.38234 ≤ C6a := by
  sorry

/-- Lower bound from [L2023] (2023). -/
@[category research solved, AMS 5]
theorem c6a_lower_bound_l2023 : 0.38271 ≤ C6a := by
  sorry

/-- Upper bound from [F1995] (1995). Conjectured (in 1976) to be optimal -/
@[category research solved, AMS 5]
theorem c6a_upper_bound_f1995 : C6a ≤ 1 / 2 := by
  refine Real.sSup_le ?_ (by norm_num)
  intro c hc
  obtain ⟨i, hi⟩ := hc 1 {∅, {0}} ⟨∅, by simp⟩ (by decide) (by decide)
  have hsub : ({∅, {0}} : Finset (Finset (Fin 1))).filter (fun x => i ∈ x) ⊆ {{0}} := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx.1 with rfl | rfl
    · exact absurd hx.2 (by simp)
    · rfl
  have h1 : ((({∅, {0}} : Finset (Finset (Fin 1))).filter (fun x => i ∈ x)).card : ℝ) ≤ 1 := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_singleton _)
  have h2 : ({∅, {0}} : Finset (Finset (Fin 1))).card = 2 := by
    rw [Finset.card_pair]; simp
  rw [h2] at hi
  push_cast at hi
  linarith

/-- What is the exact value of the constant? -/
@[category research open, AMS 5]
theorem c6a_eq : answer(sorry) = C6a := by
  sorry

end Constant6a
