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
import FormalConjectures.Wikipedia.Sendov

/-!
# Tao's Optimization constant 69a / The Sendov radius constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 69a](https://teorth.github.io/optimizationproblems/constants/69a.html)
- [Tao2022] Tao, T. "Sendov's conjecture for sufficiently high degree polynomials." Acta
  Mathematica 229 (2022), 347–392. [arXiv:2012.04125](https://arxiv.org/abs/2012.04125)

The hypotheses of Sendov's conjecture are formalised in `FormalConjectures.Wikipedia.Sendov` as
`Sendov.Polynomial.IsSendov`.
-/

open Polynomial

namespace Constant69a

/-- **Tao's Optimization constant 69a / The Sendov radius constant**:
the infimum of the radii $R$ such that, for every polynomial $f$ of degree at least $2$ whose
roots all lie in the closed unit disc, every root of $f$ is within distance $R$ of a critical
point of $f$. **Sendov's conjecture** is the statement that this constant is at most $1$. -/
@[optimization_constant "69a"]
noncomputable def C69a : ℝ :=
  sInf {R : ℝ | 0 < R ∧ ∀ f : ℂ[X], Sendov.Polynomial.IsSendov f →
    ∀ z ∈ f.rootSet ℂ, Metric.infDist z (f.derivative.rootSet ℂ) ≤ R}

/-- Lower bound from [Tao2022] (2012). Example $f(z)=z^n-1$, $\lambda_0=1$: the critical points are
at $0$ and lie on $\partial D(\lambda_0,1)$. [Tao2022-example-zn1] -/
@[category research solved, AMS 12 30 52]
theorem c69a_lower_bound_tao2022 : 1 ≤ C69a := by
  sorry

/-- Trivial upper bound. Trivial geometric bound since all zeroes of $f$ and $f'$ lie in the closed
unit disk. -/
@[category research solved, AMS 12 30 52]
theorem c69a_upper_bound_trivial : C69a ≤ 2 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 12 30 52]
theorem c69a_eq : answer(sorry) = C69a := by
  sorry

end Constant69a
