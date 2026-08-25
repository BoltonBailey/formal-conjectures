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
- [Tao2006] Tao, Terence. "247A Notes 3: Maximal theorem of Hardy-Littlewood." Lecture notes (Fall
  2006). [Author PDF](https://www.math.ucla.edu/~tao/247a.1.06f/notes3.pdf)
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

/-- Lower bound from [Ald2000] (2000). Aldaz's Proposition 1.4 gives a lower bound in every
dimension $n\ge 2$. Specializing the formula to $n=2$ gives the displayed value. [Ald2000-prop1.4]
-/
@[category research solved, AMS 42]
theorem c47a_lower_bound_ald2000 : 3 / 4 - Real.sqrt 2 / 4 + Real.sqrt 6 / 2 ≤ C47a := by
  sorry

/-- Lower bound from [Mel2003], [Ald2011] (2003, 2011). Melas proved $c_1=\dfrac{11+\sqrt{61}}{12}$.
Since $c_{d+1}\ge c_d$, we get $c_2\ge c_1$. [Mel2003-c1-formula] [Ald2011-monotone] -/
@[category research solved, AMS 42]
theorem c47a_lower_bound_mel2003_ald2011 : (11 + Real.sqrt 61) / 12 ≤ C47a := by
  sorry

/-- Upper bound from [Tao2010] (2010). The Vitali-covering proof can be sharpened from $3^d$ to
$2^d$ by covering centers with $(2+\varepsilon)$-dilates of a disjoint subcollection and letting
$\varepsilon\downarrow 0$. The same argument applies to $\ell_\infty$ balls, i.e. axis-parallel
cubes; hence $c_2\le 2^2=4$. [Tao2010-ex42] -/
@[category research solved, AMS 42]
theorem c47a_upper_bound_tao2010 : C47a ≤ 4 := by
  sorry

/-- Upper bound from [Tao2006] (2006). The standard covering-lemma proof gives an explicit constant
$3^d$ in the weak-type $(1,1)$ inequality, and the same argument applies to cubes; hence $c_2\le
3^2=9$. [Tao2006-weak-3d] [Tao2006-cubes] -/
@[category research solved, AMS 42]
theorem c47a_upper_bound_tao2006 : C47a ≤ 9 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 42]
theorem c47a_eq : answer(sorry) = C47a := by
  sorry

end Constant47a
