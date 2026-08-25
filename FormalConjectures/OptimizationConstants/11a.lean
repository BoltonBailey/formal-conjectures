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
# Tao's Optimization constant 11a / The $L^1$ Poincaré constant on the Hamming cube

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 11a](https://teorth.github.io/optimizationproblems/constants/11a.html)
- [Pisier1986] Pisier, G. "Probabilistic methods in the geometry of Banach spaces." Probability
  and Analysis, Lecture Notes in Mathematics 1206 (1986), 167–241.
- [BELP2008] Ben Efraim, L.; Lust-Piquard, F. "Poincaré type inequalities on the discrete cube
  and in the CAR algebra." Probability Theory and Related Fields 141 (2008), 569–602.
- [ILvHV2019] Ivanisvili, P.; van Handel, R.; Volberg, A. Improvement over $\pi/2$, 2019.
- [IS2024] Ivanisvili, P.; Stone, ... Explicit $\delta \approx 0.00013$, 2024.
-/

namespace Constant11a

variable {n : ℕ}

/-- Flip the $j$-th coordinate of a point of the discrete cube, which we model as
`Fin n → Bool`. -/
def flipAt (x : Fin n → Bool) (j : Fin n) : Fin n → Bool := Function.update x j (!x j)

/-- The discrete derivative $D_j f(x) = (f(x) - f(x^{(j)})) / 2$. -/
noncomputable def discreteDeriv (f : (Fin n → Bool) → ℝ) (j : Fin n) (x : Fin n → Bool) : ℝ :=
  (f x - f (flipAt x j)) / 2

/-- The length of the discrete gradient,
$|\nabla f|(x) = \left(\sum_j |D_j f(x)|^2\right)^{1/2}$. -/
noncomputable def gradNorm (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) : ℝ :=
  Real.sqrt (∑ j, discreteDeriv f j x ^ 2)

/-- The expectation of a function with respect to the uniform measure on the cube. -/
noncomputable def expect (g : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ x : Fin n → Bool, g x) / 2 ^ n

/-- **Tao's Optimization constant 11a / The $L^1$ Poincaré constant on the Hamming cube**:
the smallest constant $C$ with
$\mathbb{E}|f(x) - \mathbb{E}f(x)| \le C\,\mathbb{E}|\nabla f|(x)$
for every $n \ge 1$ and every $f : \{-1, 1\}^n \to \mathbb{R}$. -/
@[optimization_constant "11a"]
noncomputable def C11a : ℝ :=
  sInf {C : ℝ | ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ),
    expect (fun x => |f x - expect f|) ≤ C * expect (gradNorm f)}

/-- Trivial lower bound. For $n=1$, take $f(x)=x$ to get ratio $1$. -/
@[category research solved, AMS 5 60]
theorem c11a_lower_bound_trivial : 1 ≤ C11a := by
  sorry

/-- Lower bound from [Pisier1986], [ILvHV2019] (1986, 2019). Comes from the sharp Gaussian
$L^1$-Poincaré inequality (Pisier). -/
@[category research solved, AMS 5 60]
theorem c11a_lower_bound_pisier1986_ilvhv2019 : Real.sqrt (Real.pi / 2) ≤ C11a := by
  sorry

/-- Upper bound from [BELP2008] (2008). First proof (non-commutative/CAR algebra). Several later
proofs recover the same constant. -/
@[category research solved, AMS 5 60]
theorem c11a_upper_bound_belp2008 : C11a ≤ Real.pi / 2 := by
  sorry

/-- Upper bound from [ILvHV2019] (2019). The bound $\pi/2 - \delta$ for some $\delta > 0$. First
proof that $C_{11a}$ is strictly smaller than $\pi/2$. -/
@[category research solved, AMS 5 60]
theorem c11a_upper_bound_ilvhv2019 : C11a < Real.pi / 2 := by
  sorry

/-- Upper bound from [IS2024] (2024). The bound $\pi/2 - \delta$ with $\delta \approx 0.00013$,
stated here with $\delta = 0.0001$. Provides an explicit integral expression for $\delta$ and
evaluates it numerically (about $1.3\times 10^{-4}$). -/
@[category research solved, AMS 5 60]
theorem c11a_upper_bound_is2024 : C11a ≤ Real.pi / 2 - 0.0001 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 60]
theorem c11a_eq : answer(sorry) = C11a := by
  sorry

end Constant11a
