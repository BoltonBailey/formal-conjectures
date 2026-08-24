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

/-- The best known lower bound $6\pi/11 \approx 1.71360$ [SLXCKKM26]. Grothendieck's original
lower bound is $\pi/2$ [G1953]. -/
@[category research solved, AMS 46 47]
theorem c10a_lower_bound : 6 * Real.pi / 11 ≤ C10a := by
  sorry

/-- The best known explicit upper bound is Krivine's bound
$\frac{\pi}{2 \log(1 + \sqrt{2})} \approx 1.782214$ [K1979]. It is known to be non-sharp
[BMMN2011], and has been improved by $6.039 \times 10^{-5}$ in [LSXCKKM26]. -/
@[category research solved, AMS 46 47]
theorem c10a_upper_bound : C10a ≤ Real.pi / (2 * Real.log (1 + Real.sqrt 2)) := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 46 47]
theorem mem_Ico_c10a :
    answer(sorry) ∈ Set.Ico C10a (Real.pi / (2 * Real.log (1 + Real.sqrt 2))) := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 46 47]
theorem mem_Ioc_c10a : answer(sorry) ∈ Set.Ioc (6 * Real.pi / 11) C10a := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 46 47]
theorem c10a_eq : C10a = answer(sorry) := by
  sorry

end Constant10a
