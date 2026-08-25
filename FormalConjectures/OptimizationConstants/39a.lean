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

/-- Lower bound from Classical (cube). $H_3 \ge 2^3 = 8$ (already forced by the cube /
parallelotope). [ABP2024-lb-cube] -/
@[category research solved, AMS 52]
theorem c39a_lower_bound_classical : 8 ≤ C39a := by
  sorry

/-- Upper bound from [Pap1999] (1999). Previous best bound: $H_3 \le 16$ (Papadoperakis).
[ABP2024-ub-H3-16] -/
@[category research solved, AMS 52]
theorem c39a_upper_bound_pap1999 : C39a ≤ 16 := by
  sorry

/-- Upper bound from [Pry2023] (2023). Best known general upper bound: $H_3 \le 14$ (attributed to
Prymak). [ABP2024-ub-H3-14] -/
@[category research solved, AMS 52]
theorem c39a_upper_bound_pry2023 : C39a ≤ 14 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 52]
theorem c39a_eq : answer(sorry) = C39a := by
  sorry

end Constant39a
