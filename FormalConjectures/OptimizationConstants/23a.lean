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
import FormalConjectures.Wikipedia.Hadamard

/-!
# Tao's Optimization constant 23a / The smallest unsolved instance of the Hadamard conjecture

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 23a](https://teorth.github.io/optimizationproblems/constants/23a.html)
- [CP2024] Ćustić, A.; Ponomarenko, V. Survey of known Hadamard matrix orders; the smallest
  order for which no Hadamard matrix is known is $668$.

Hadamard matrices are formalised in `FormalConjectures.Wikipedia.Hadamard` as
`Hadamard.IsHadamard`.
-/

namespace Constant23a

/-- **Tao's Optimization constant 23a / The smallest unsolved instance of the Hadamard
conjecture**: the smallest $n$ divisible by $4$ for which there is no Hadamard matrix of order
$n$, or $\infty$ if no such $n$ exists. The **Hadamard conjecture** asserts that it is
$\infty$. -/
@[optimization_constant "23a"]
noncomputable def C23a : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ k : ℕ, n = 4 * k ∧ ¬ ∃ M, Hadamard.IsHadamard (n := 4 * k) M}

/-- Trivial lower bound. By definition $C_{23a}$ (if finite) is a multiple of $4$. -/
@[category research solved, AMS 5 15]
theorem c23a_lower_bound_trivial : 4 ≤ C23a := by
  refine le_sInf ?_
  rintro n ⟨k, rfl, hk⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exact absurd (show ∃ M, Hadamard.IsHadamard (n := 4 * 0) M from
      Hadamard.exists_hadamard_zero) hk
  · have h4 : (4 : ℕ∞) * (k : ℕ∞) = ((4 * k : ℕ) : ℕ∞) := by push_cast; ring
    rw [h4]
    exact_mod_cast Nat.le_mul_of_pos_right 4 hkpos

/-- Lower bound from [CP2024] (2025). All orders $n<668$ with $n\equiv 0\pmod4$ are known to admit
Hadamard matrices; the smallest currently unresolved order is $668$. -/
@[category research solved, AMS 5 15]
theorem c23a_lower_bound_cp2024 : 668 ≤ C23a := by
  sorry

/-- Trivial upper bound. No finite upper bound is known; conjecturally sharp (Hadamard conjecture).
-/
@[category research solved, AMS 5 15]
theorem c23a_upper_bound_trivial : C23a ≤ ⊤ := by
  exact le_top

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 15]
theorem c23a_eq : answer(sorry) = C23a := by
  sorry

end Constant23a
