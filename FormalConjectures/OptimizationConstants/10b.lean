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
# Tao's Optimization constant 10b / The complex Grothendieck constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 10b](https://teorth.github.io/optimizationproblems/constants/10b.html)
- [D1984] Davie, A. M. Lower bound for the complex Grothendieck constant, 1984.
- [H1987] Haagerup, U. "A new upper bound for the complex Grothendieck constant." Israel Journal
  of Mathematics 60 (1987), 199–224.
- [P1978] Pisier, G. "Grothendieck's theorem for noncommutative $C^*$-algebras." Journal of
  Functional Analysis 29 (1978), 397–415.
-/

namespace Constant10b

/-- The maximum modulus of the bilinear form $\sum_{i,j} a_{ij} s_i t_j$ over unimodular
scalars. -/
noncomputable def phaseValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ s : Fin m → ℂ, ∃ t : Fin n → ℂ,
    (∀ i, ‖s i‖ = 1) ∧ (∀ j, ‖t j‖ = 1) ∧ r = ‖∑ i, ∑ j, A i j * s i * t j‖}

/-- **Tao's Optimization constant 10b / The complex Grothendieck constant**
$K_G^{\mathbb{C}}$: the smallest $C$ such that for every complex matrix $A$ and all unit vectors
$u_i, v_j$ in a complex Hilbert space,
$\left|\sum_{i,j} a_{ij} \langle u_i, v_j \rangle\right| \le C \max_{|s_i| = |t_j| = 1}
\left|\sum_{i,j} a_{ij} s_i t_j\right|$. -/
@[optimization_constant "10b"]
noncomputable def C10b : ℝ :=
  sInf {C : ℝ | ∀ (m n d : ℕ) (A : Matrix (Fin m) (Fin n) ℂ)
      (u : Fin m → EuclideanSpace ℂ (Fin d)) (v : Fin n → EuclideanSpace ℂ (Fin d)),
    (∀ i, ‖u i‖ = 1) → (∀ j, ‖v j‖ = 1) →
      ‖∑ i, ∑ j, A i j * inner ℂ (u i) (v j)‖ ≤ C * phaseValue A}

/-- The best known lower bound $1.338$, due to Davie [D1984]. -/
@[category research solved, AMS 46 47]
theorem c10b_lower_bound : 1.338 ≤ C10b := by
  sorry

/-- The best known upper bound $1.40491$, proven by Haagerup in [H1987]. Pisier [P1978] gave
$e^{1 - \gamma} \approx 1.52621$. -/
@[category research solved, AMS 46 47]
theorem c10b_upper_bound : C10b ≤ 1.40491 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 46 47]
theorem mem_Ico_c10b : answer(sorry) ∈ Set.Ico C10b 1.40491 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 46 47]
theorem mem_Ioc_c10b : answer(sorry) ∈ Set.Ioc 1.338 C10b := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 46 47]
theorem c10b_eq : C10b = answer(sorry) := by
  sorry

end Constant10b
