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
import FormalConjectures.Wikipedia.Brennanconjecture

/-!
# Tao's Optimization constant 67a / Brennan's conjecture exponent

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 67a](https://teorth.github.io/optimizationproblems/constants/67a.html)
- [Bre1978] Brennan, J. E. "The integrability of the derivative in conformal mapping." Journal of
  the London Mathematical Society 18 (1978), 261–272.
- [Ber1999] Bertilsson, D. "On Brennan's conjecture in conformal mapping." Doctoral thesis, KTH,
  1999.
- [HC2015] Hedenmalm, H.; Chen, S. Historical summary of Brennan's conjecture, 2015.

An equivalent formulation, in terms of the universal integral means spectrum, is formalised in
`FormalConjectures.Wikipedia.Brennanconjecture`: Brennan's conjecture is the statement
`BrennanConjecture.universalSpectrum (-2) = 1`.
-/

open MeasureTheory Set

namespace Constant67a

/-- **Tao's Optimization constant 67a / Brennan's conjecture exponent**:
the supremum of the exponents $p$ such that $\int_\Omega |\varphi'(z)|^p\,dx\,dy < \infty$ for
every simply connected $\Omega \subsetneq \mathbb{C}$ and every conformal map
$\varphi : \Omega \to \mathbb{D}$. The requirement that $\varphi$ maps $\Omega$ bijectively onto
the unit disc already forces $\Omega$ to have at least two boundary points in the extended
plane, by the Riemann mapping theorem. -/
@[optimization_constant "67a"]
noncomputable def C67a : ℝ :=
  sSup {p : ℝ | ∀ (Ω : Set ℂ) (φ : ℂ → ℂ), IsOpen Ω → IsConnected Ω →
    SimplyConnectedSpace Ω →
    AnalyticOn ℂ φ Ω → InjOn φ Ω → φ '' Ω = BrennanConjecture.unitDisk →
      IntegrableOn (fun z => ‖deriv φ z‖ ^ p) Ω}

/-- Trivial lower bound. Trivial by change of variables:
$\int_{\Omega}\lvert\varphi'(z)\rvert^2\,dA(z)=\mathrm{Area}(\mathbb{D})=\pi$. -/
@[category research solved, AMS 30]
theorem c67a_lower_bound_trivial : 2 ≤ C67a := by
  sorry

/-- Lower bound from [HC2015] (2015). Historical summary attributes this threshold to Bertilsson's
dissertation. [HC2015-best-known-3-422] -/
@[category research solved, AMS 30]
theorem c67a_lower_bound_hc2015 : 3.422 ≤ C67a := by
  sorry

/-- Upper bound from [HC2015] (2015). Conjectured endpoint. [HC2015-conjecture-range] -/
@[category research solved, AMS 30]
theorem c67a_upper_bound_hc2015 : C67a ≤ 4 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 30]
theorem c67a_eq : answer(sorry) = C67a := by
  sorry

end Constant67a
