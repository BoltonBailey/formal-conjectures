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
# Tao's Optimization constant 39a / The Hadwiger covering number in dimension 3

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 39a](https://teorth.github.io/optimizationproblems/constants/39a.html)
- [Pap1999] Papadoperakis, I. "An estimate for the problem of illumination of the boundary of a
  convex body in $E^3$." Geometriae Dedicata 75 (1999), 275–285.
- [Pry2023] Prymak, A. "A new bound for Hadwiger's covering problem in $\mathbb{E}^3$." SIAM
  Journal on Discrete Mathematics 37 (2023), 17–24.
- [ABP2024] Arman, A.; Bondarenko, A.; Prymak, A. Survey of the Hadwiger covering problem, 2024.
-/

namespace Constant39a

/-- The minimal number of translates of $L$ needed to cover $K$. -/
noncomputable def coveringNumber (K L : Set (EuclideanSpace ℝ (Fin 3))) : ℕ :=
  sInf {m : ℕ | ∃ t : Fin m → EuclideanSpace ℝ (Fin 3), K ⊆ ⋃ i, (fun x => x + t i) '' L}

/-- **Tao's Optimization constant 39a / The Hadwiger covering number in dimension 3**:
the least $H_3$ such that every three-dimensional convex body can be covered by $H_3$ translates
of its interior. -/
@[optimization_constant "39a"]
noncomputable def C39a : ℕ :=
  sSup {m : ℕ | ∃ K : Set (EuclideanSpace ℝ (Fin 3)), IsCompact K ∧ Convex ℝ K ∧
    (interior K).Nonempty ∧ m = coveringNumber K (interior K)}

/-- The lower bound $8 = 2^3$, already forced by the cube. -/
@[category research solved, AMS 52]
theorem c39a_lower_bound : 8 ≤ C39a := by
  sorry

/-- The best known upper bound $14$, proven by Prymak in [Pry2023], improving the bound $16$ of
Papadoperakis [Pap1999]. -/
@[category research solved, AMS 52]
theorem c39a_upper_bound : C39a ≤ 14 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ico_c39a : answer(sorry) ∈ Set.Ico C39a 14 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 52]
theorem mem_Ioc_c39a : answer(sorry) ∈ Set.Ioc 8 C39a := by
  sorry

/-- What is the exact value of the constant? **Hadwiger's covering (illumination) conjecture**
asserts that $H_n = 2^n$ for every $n$, hence that this constant is $8$ [ABP2024]. -/
@[category research open, AMS 52]
theorem c39a_eq : C39a = answer(sorry) := by
  sorry

end Constant39a
