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
import FormalConjectures.Wikipedia.KomlosConjecture

/-!
# Tao's Optimization constant 24a / The Komlós discrepancy constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 24a](https://teorth.github.io/optimizationproblems/constants/24a.html)
- [Ban1998] Banaszczyk, W. "Balancing vectors and Gaussian measures of $n$-dimensional convex
  bodies." Random Structures & Algorithms 12 (1998), 351–360.
- [Kun2023] Kunisky, D. "A lower bound for the Komlós conjecture constant." 2023.
- [BJ2025] Bansal, N.; Jiang, H. "Improved bounds for the Komlós problem." 2025.
- [Bec1981] Beck, J. "Roth’s estimate of the discrepancy of integer sequences is nearly sharp."
  Combinatorica 1(4) (1981), 319–325.
- [Spe1985] Spencer, J. "Six standard deviations suffice." Trans. Amer. Math. Soc. 289(2) (1985),
  679–706. # Acknowledgements Prepared with assistance from ChatGPT 5.2 Pro.
- [Glu1989] Gluskin, E. D. "Extremal properties of orthogonal parallelepipeds and their applications
  to the theory of Banach spaces." Mat. Sb. (N.S.) *"136(178)"*(1) (1988), 85–96; English transl.:
  Math. USSR-Sb. 64(1) (1989), 85–96.
- [BDG2019] Bansal, N.; Dadush, D.; Garg, S. "An algorithm for Komlós conjecture matching
  Banaszczyk’s bound." SIAM J. Comput. 48(2) (2019), 534–553.
  [arXiv:1605.02882](https://arxiv.org/abs/1605.02882).

The Komlós conjecture is formalised in `FormalConjectures.Wikipedia.KomlosConjecture`.
-/

open scoped ENNReal

namespace Constant24a

/-- The dimension-$n$ Komlós discrepancy $K_n$: the supremum of $\min_{x \in \{-1,1\}^n}
\|Ax\|_\infty$ over real $n \times n$ matrices $A$ whose columns have Euclidean norm at
most $1$. -/
noncomputable def K (n : ℕ) : ℝ≥0∞ :=
  ⨆ A : {A : Matrix (Fin n) (Fin n) ℝ // ∀ j, ∑ i, (A i j) ^ 2 ≤ 1},
    ENNReal.ofReal (sInf {r : ℝ | ∃ x : Fin n → ℝ, (∀ j, x j = 1 ∨ x j = -1) ∧
      r = ⨆ i, |∑ j, (A : Matrix (Fin n) (Fin n) ℝ) i j * x j|})

/-- **Tao's Optimization constant 24a / The Komlós discrepancy constant**:
$\sup_{n \ge 1} K_n$. The **Komlós conjecture** asserts that this constant is finite. -/
@[optimization_constant "24a"]
noncomputable def C24a : ℝ≥0∞ := ⨆ n : ℕ, K n

/-- Trivial lower bound. Take $n=1$ and $A=[1]$, for which $\mathrm{disc}(A)=1$. -/
@[category research solved, AMS 5 11]
theorem c24a_lower_bound_trivial : 1 ≤ C24a := by
  refine le_iSup_of_le 1 (le_iSup_of_le ⟨1, fun j => ?_⟩ ?_)
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [Matrix.one_apply]
  · have hS : {r : ℝ | ∃ x : Fin 1 → ℝ, (∀ j, x j = 1 ∨ x j = -1) ∧
        r = ⨆ i, |∑ j, (1 : Matrix (Fin 1) (Fin 1) ℝ) i j * x j|} = {1} := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [ciSup_unique]
        simp only [Matrix.one_apply, one_mul]
        rcases hx 0 with h | h <;> simp [h]
      · rintro rfl
        refine ⟨fun _ => 1, fun j => Or.inl rfl, ?_⟩
        rw [ciSup_unique]
        simp [Matrix.one_apply]
    rw [hS, csInf_singleton, ENNReal.ofReal_one]

/-- Lower bound from [Kun2023] (2023). Best known lower bound on $C_{24}$. -/
@[category research solved, AMS 5 11]
theorem c24a_lower_bound_kun2023 : ENNReal.ofReal (1 + Real.sqrt 2) ≤ C24a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c24a_eq : answer(sorry) = C24a := by
  sorry

/-- **The Komlós conjecture**: is the constant finite? -/
@[category research open, AMS 5 11]
theorem c24a_ne_top : C24a ≠ ⊤ := by
  sorry

-- Note: the "Known upper bounds" table on the website records bounds on $K_n$ for each
-- fixed $n$ (e.g. $O(\sqrt{\log n})$), not bounds on the constant itself; no finite upper bound
-- on the constant is known, so these rows are not formalised here.

end Constant24a
