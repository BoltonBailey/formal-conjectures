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
# Tao's Optimization constant 10a / The real Grothendieck constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 10a](https://teorth.github.io/optimizationproblems/constants/10a.html)
- [G1953] Grothendieck, A. "Résumé de la théorie métrique des produits tensoriels topologiques."
  Bol. Soc. Mat. São Paulo 8 (1953), 1–79.
- [K1979] Krivine, J.-L. "Constantes de Grothendieck et fonctions de type positif sur les
  sphères." Advances in Mathematics 31 (1979), 16–30.
- [BMMN2011] Braverman, M.; Makarychev, K.; Makarychev, Y.; Naor, A. "The Grothendieck constant
  is strictly smaller than Krivine's bound." Forum of Mathematics Pi 1 (2013), e4.
- [SLXCKKM26] Lower bound $6\pi/11$, 2026.
- [LSXCKKM26] Upper bound improving Krivine's bound by $6.039 \times 10^{-5}$, 2026.
- [Dav1984] Davie, A. M. "Lower bound for $K_{G}$." Unpublished note (1984).
- [Ree1991] Reeds, James A. "A new lower bound on the real Grothendieck constant." Unpublished
  manuscript (1991).
- [Hei26] Heilman, Steven. "A lower bound for Grothendieck's constant." (2026)
  [arXiv:2603.22616](https://arxiv.org/abs/2603.22616)
- [JM26] Jones, Chris; Malavolta, Giulio. "The Grothendieck constant is strictly larger than
  Davie-Reeds' bound." (2026) [arXiv:2603.30039](https://arxiv.org/abs/2603.30039)
- [R1974] Rietz, Ronald E. "A proof of the Grothendieck inequality." Israel J. Math. 19 (1974),
  271–276.
- [Hei26b] Heilman, Steven. "An Upper Bound on Grothendieck's constant." (2026)
  [arXiv:2606.00247](https://arxiv.org/abs/2606.00247)
-/

open RealInnerProductSpace

namespace Constant10a

/-- The maximum of the bilinear form $\sum_{i,j} a_{ij} \varepsilon_i \delta_j$ over sign
vectors. -/
noncomputable def signValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup {s : ℝ | ∃ ε : Fin m → ℝ, ∃ δ : Fin n → ℝ,
    (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ j, δ j = 1 ∨ δ j = -1) ∧
    s = ∑ i, ∑ j, A i j * ε i * δ j}

/-- **Tao's Optimization constant 10a / The real Grothendieck constant** $K_G^{\mathbb{R}}$:
the smallest $C$ such that for every real matrix $A$ and all unit vectors $u_i, v_j$ in a real
Hilbert space, $\sum_{i,j} a_{ij} \langle u_i, v_j \rangle \le C \max_{\varepsilon, \delta = \pm 1}
\sum_{i,j} a_{ij} \varepsilon_i \delta_j$. -/
@[optimization_constant "10a"]
noncomputable def C10a : ℝ :=
  sInf {C : ℝ | ∀ (m n d : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
      (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d)),
    (∀ i, ‖u i‖ = 1) → (∀ j, ‖v j‖ = 1) →
      ∑ i, ∑ j, A i j * ⟪u i, v j⟫ ≤ C * signValue A}

/-- Trivial lower bound. Follows from the definitions -/
@[category research solved, AMS 46 47]
theorem c10a_lower_bound_trivial : 1 ≤ C10a := by
  sorry

/-- Lower bound from [G1953] (1953). Grothendieck’s original lower bound -/
@[category research solved, AMS 46 47]
theorem c10a_lower_bound_g1953 : Real.pi / 2 ≤ C10a := by
  sorry

/-- Lower bound from [Dav1984], [Ree1991] (1984, 1991). Here $K_{DR} = 1.676956\ldots$ is the
Davie-Reeds constant, stated with the truncation $1.67695$. Davie–Reeds lower bound -/
@[category research solved, AMS 46 47]
theorem c10a_lower_bound_dav1984_ree1991 : 1.67695 ≤ C10a := by
  sorry

/-- Lower bound from [Hei26] (2026). Here $K_{DR} = 1.676956\ldots$ is the Davie-Reeds constant,
stated with the truncation $1.67695$. Concurrent 2026 improvement over the Davie–Reeds bound -/
@[category research solved, AMS 46 47]
theorem c10a_lower_bound_hei26 : 1.67695 + 10 ^ (-26 : ℤ) ≤ C10a := by
  sorry

/-- Lower bound from [JM26] (2026). Here $K_{DR} = 1.676956\ldots$ is the Davie-Reeds constant,
stated with the truncation $1.67695$. Strict improvement over the Davie–Reeds bound -/
@[category research solved, AMS 46 47]
theorem c10a_lower_bound_jm26 : 1.67695 + 10 ^ (-12 : ℤ) ≤ C10a := by
  sorry

/-- Lower bound from [SLXCKKM26] (2026). Major jump over the Davie–Reeds anchor $\approx 1.67696$;
proved by establishing asymptotic limitations of Krivine schemes rather than by constructing
explicit gap instances (as all prior lower bounds did). Together with the upper bound above, this
determines the tenths digit of $K_G^{\mathbb R}$ to be $7$. -/
@[category research solved, AMS 46 47]
theorem c10a_lower_bound_slxckkm26 : (6 * Real.pi) / 11 ≤ C10a := by
  sorry

/-- Upper bound from [G1953] (1953). Grothendieck’s original upper bound -/
@[category research solved, AMS 46 47]
theorem c10a_upper_bound_g1953 : C10a ≤ Real.sinh (Real.pi / 2) := by
  sorry

/-- Upper bound from [R1974] (1974). Improvement of the original upper bound -/
@[category research solved, AMS 46 47]
theorem c10a_upper_bound_r1974 : C10a ≤ 2.261 := by
  sorry

/-- Upper bound from [K1979] (1979). Krivine’s bound; best known **explicit** numerical upper bound
-/
@[category research solved, AMS 46 47]
theorem c10a_upper_bound_k1979 : C10a ≤ Real.pi / (2 * Real.log (1 + Real.sqrt 2)) := by
  sorry

/-- Upper bound from [BMMN2011] (2013). Strict improvement over Krivine’s bound -/
@[category research solved, AMS 46 47]
theorem c10a_upper_bound_bmmn2011 : C10a < Real.pi / (2 * Real.log (1 + Real.sqrt 2)) := by
  sorry

/-- Upper bound from [Hei26b] (2026). $10^{-5}$ improvement over Krivine's bound -/
@[category research solved, AMS 46 47]
theorem c10a_upper_bound_hei26b :
    C10a < (Real.pi / (2 * Real.log (1 + Real.sqrt 2))) - 10 ^ (-5 : ℤ) := by
  sorry

/-- Upper bound from [LSXCKKM26] (2026). $6.039\times 10^{-5}$ improvement over Krivine's bound -/
@[category research solved, AMS 46 47]
theorem c10a_upper_bound_lsxckkm26 :
    C10a < (Real.pi / (2 * Real.log (1 + Real.sqrt 2))) - 6.039 * 10 ^ (-5 : ℤ) := by
  sorry

/-- Upper bound from [SLXCKKM26] (2026). Same team; via the first *asymptotic* Krivine-type rounding
scheme (previous works only considered low-dimensional schemes). -/
@[category research solved, AMS 46 47]
theorem c10a_upper_bound_slxckkm26 :
    C10a < (Real.pi / (2 * Real.log (1 + Real.sqrt 2))) - 10 ^ (-4 : ℤ) := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 46 47]
theorem c10a_eq : answer(sorry) = C10a := by
  sorry

end Constant10a
