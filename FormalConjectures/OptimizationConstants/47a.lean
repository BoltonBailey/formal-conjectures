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
# Tao's Optimization constant 47a / The centered Hardy-Littlewood maximal constant in dimension 2

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 47a](https://teorth.github.io/optimizationproblems/constants/47a.html)
- [Mel2003] Melas, A. D. "The best constant for the centered Hardy-Littlewood maximal
  inequality." Annals of Mathematics 157 (2003), 647–688.
- [Ald2000] Aldaz, J. M. "Remarks on the Hardy-Littlewood maximal function." Proceedings of the
  Royal Society of Edinburgh Section A 128 (1998), 1–9.
- [Ald2011] Aldaz, J. M. "The weak type (1,1) bounds for the maximal function associated to
  cubes grow to infinity with the dimension." Annals of Mathematics 173 (2011), 1013–1023.
- [Tao2010] Tao, T. Lecture notes on the Vitali covering argument, 2010.
-/

open MeasureTheory

namespace Constant47a

/-- The closed axis-parallel cube of centre `x` and radius `r` in $\mathbb{R}^2$, i.e. the
$\ell^\infty$ ball. -/
def cube (x : Fin 2 → ℝ) (r : ℝ) : Set (Fin 2 → ℝ) :=
  Set.Icc (fun i => x i - r) (fun i => x i + r)

/-- The centered Hardy-Littlewood maximal function associated to axis-parallel cubes. -/
noncomputable def maximalFn (f : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  sSup {a : ℝ | ∃ r > (0 : ℝ), a = (∫ y in cube x r, |f y|) / (2 * r) ^ 2}

/-- **Tao's Optimization constant 47a / The centered Hardy-Littlewood maximal constant in
dimension 2**: the smallest $c$ such that
$\alpha\,|\{x : M f(x) \ge \alpha\}| \le c\,\|f\|_1$ for every $f \in L^1(\mathbb{R}^2)$ and
every $\alpha > 0$, where $M$ is the maximal operator associated to axis-parallel squares. -/
@[optimization_constant "47a"]
noncomputable def C47a : ℝ :=
  sInf {c : ℝ | ∀ f : (Fin 2 → ℝ) → ℝ, Integrable f → ∀ α > (0 : ℝ),
    α * (volume {x | α ≤ maximalFn f x}).toReal ≤ c * ∫ y, |f y|}

/-- The best known lower bound $\frac34 - \frac{\sqrt 2}{4} + \frac{\sqrt 6}{2} \approx
1.6211915$, from Aldaz's construction [Ald2000]. Melas [Mel2003] determined the one-dimensional
constant $\frac{11 + \sqrt{61}}{12}$, which is also a lower bound by monotonicity in the
dimension. -/
@[category research solved, AMS 42]
theorem c47a_lower_bound :
    3 / 4 - Real.sqrt 2 / 4 + Real.sqrt 6 / 2 ≤ C47a := by
  sorry

/-- The best known upper bound $4 = 2^2$, from the sharpened Vitali covering argument
[Tao2010]. The standard covering lemma gives $3^2 = 9$. -/
@[category research solved, AMS 42]
theorem c47a_upper_bound : C47a ≤ 4 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 42]
theorem mem_Ico_c47a : answer(sorry) ∈ Set.Ico C47a 4 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 42]
theorem mem_Ioc_c47a :
    answer(sorry) ∈ Set.Ioc (3 / 4 - Real.sqrt 2 / 4 + Real.sqrt 6 / 2) C47a := by
  sorry

/-- What is the exact value of the constant? No best constant is known in any dimension greater
than one [Ald2011]. -/
@[category research open, AMS 42]
theorem c47a_eq : C47a = answer(sorry) := by
  sorry

end Constant47a
