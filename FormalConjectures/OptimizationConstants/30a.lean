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
# Tao's Optimization constant 30a / The Stanley-Wilf limit for the pattern 1324

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 30a](https://teorth.github.io/optimizationproblems/constants/30a.html)
- [B04] Bóna, M. "The limit of a Stanley-Wilf sequence is not always rational, and layered
  patterns beat monotone patterns." Journal of Combinatorial Theory Series A 110 (2005), 223–235.
- [CJS12] Claesson, A.; Jelínek, V.; Steingrímsson, E. "Upper bounds for the Stanley-Wilf limit
  of 1324 and other layered patterns." Journal of Combinatorial Theory Series A 119 (2012),
  1680–1691.
- [BBEPP2017] Bevan, D.; Brignall, R.; Elvey Price, A.; Pantone, J. "A structural
  characterisation of $\mathrm{Av}(1324)$ and new bounds on its growth rate." European Journal of
  Combinatorics 88 (2020), 103115. [arXiv:1711.10325](https://arxiv.org/abs/1711.10325)
-/

open Filter

namespace Constant30a

/-- The pattern $1324$, as an order-defining function on four points. -/
def pattern1324 : Fin 4 → Fin 4 := ![0, 2, 1, 3]

/-- A permutation of $\{1, \ldots, n\}$ **avoids** the pattern $1324$ if there are no indices
$i_1 < i_2 < i_3 < i_4$ on which it is order-isomorphic to $1324$. -/
def Avoids1324 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ¬ ∃ f : Fin 4 → Fin n, StrictMono f ∧
    ∀ a b : Fin 4, pattern1324 a < pattern1324 b ↔ σ (f a) < σ (f b)

/-- $S_n(1324)$, the number of permutations of $\{1, \ldots, n\}$ avoiding the pattern
$1324$. -/
noncomputable def S (n : ℕ) : ℕ := Nat.card {σ : Equiv.Perm (Fin n) // Avoids1324 σ}

/-- **Tao's Optimization constant 30a / The Stanley-Wilf limit for the pattern 1324**:
$\lim_n S_n(1324)^{1/n}$. The limit is known to exist by Marcus-Tardos and Arratia; we take a
`limsup` so that the definition does not presuppose this. -/
@[optimization_constant "30a"]
noncomputable def C30a : ℝ := limsup (fun n : ℕ => (S n : ℝ) ^ ((n : ℝ)⁻¹)) atTop

/-- The best known lower bound $10.27$, proven by Bevan-Brignall-Elvey Price-Pantone
in [BBEPP2017]. -/
@[category research solved, AMS 5]
theorem c30a_lower_bound : 10.27 ≤ C30a := by
  sorry

/-- The best known upper bound $13.5$, proven by Bevan-Brignall-Elvey Price-Pantone
in [BBEPP2017]. Claesson-Jelínek-Steingrímsson [CJS12] gave $16$, improving Bóna's $288$
[B04]. -/
@[category research solved, AMS 5]
theorem c30a_upper_bound : C30a ≤ 13.5 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 5]
theorem mem_Ico_c30a : answer(sorry) ∈ Set.Ico C30a 13.5 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5]
theorem mem_Ioc_c30a : answer(sorry) ∈ Set.Ioc 10.27 C30a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5]
theorem c30a_eq : C30a = answer(sorry) := by
  sorry

end Constant30a
