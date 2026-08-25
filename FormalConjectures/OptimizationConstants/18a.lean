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
import FormalConjectures.GreensOpenProblems.«49»

/-!
# Tao's Optimization constant 18a / Marton's conjecture (Polynomial Freiman-Ruzsa) constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 18a](https://teorth.github.io/optimizationproblems/constants/18a.html)
- [GGMT2025] Gowers, W. T.; Green, B. J.; Manners, F.; Tao, T. "On a conjecture of Marton."
  Annals of Mathematics 201 (2025), no. 2, 515–549.
- [L2024] Liu, Y. "A simple proof of the Polynomial Freiman-Ruzsa conjecture with an improved
  constant." 2024.

The qualitative form of the conjecture is formalised in
`FormalConjectures.GreensOpenProblems.«49»`.
-/

open scoped Pointwise Finset

namespace Constant18a

/-- **Tao's Optimization constant 18a / Marton's conjecture (Polynomial Freiman-Ruzsa)
constant**: the least $C$ such that every $A \subseteq \mathbb{F}_2^n$ with
$|A + A| \le K|A|$ can be covered by $K^{C + o(1)}$ cosets of a subspace of size at most $|A|$,
where $o(1)$ is taken as $K \to \infty$. -/
@[optimization_constant "18a"]
noncomputable def C18a : ℝ :=
  sInf {C : ℝ | ∀ ε > 0, ∃ K₀ ≥ (1 : ℝ), ∀ K ≥ K₀,
    ∀ n (A : Finset (𝔽₂ n)), A.Nonempty → (#(A + A) : ℝ) ≤ K * #A →
      ∃ (W : Submodule (ZMod 2) (𝔽₂ n)) (T : Finset (𝔽₂ n)),
        Nat.card W ≤ #A ∧ (#T : ℝ) ≤ K ^ (C + ε) ∧ (A : Set (𝔽₂ n)) ⊆ T + W}

/-- Trivial lower bound. Consider $K$ basis vectors -/
@[category research solved, AMS 5 11]
theorem c18a_lower_bound_trivial : 1 ≤ C18a := by
  sorry

/-- Upper bound from [GGMT2025] (2025). Usually reported as $12$ -/
@[category research solved, AMS 5 11]
theorem c18a_upper_bound_ggmt2025 : C18a ≤ 7 + Real.sqrt 17 := by
  sorry

/-- Upper bound from [L2024] (2024). A simplified argument giving $11$ is also provided -/
@[category research solved, AMS 5 11]
theorem c18a_upper_bound_l2024 : C18a ≤ 9 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c18a_eq : answer(sorry) = C18a := by
  sorry

end Constant18a
