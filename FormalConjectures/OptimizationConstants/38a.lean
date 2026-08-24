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
# Tao's Optimization constant 38a / The square-lattice self-avoiding walk connective constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 38a](https://teorth.github.io/optimizationproblems/constants/38a.html)
- [CG1993] Conway, A. R.; Guttmann, A. J. "Lower bound on the number of self-avoiding walks."
  Journal of Physics A 26 (1993), 1535–1542.
- [Jen2004] Jensen, I. "Improved lower bounds on the connective constants for two-dimensional
  self-avoiding walks." Journal of Physics A 37 (2004), 5503–5524.
- [PT2000] Pönitz, A.; Tittmann, P. "Improved upper bounds for self-avoiding walks in
  $\mathbb{Z}^d$." Electronic Journal of Combinatorics 7 (2000), R21.
- [FV2017] Friedli, S.; Velenik, Y. "Statistical Mechanics of Lattice Systems." Cambridge
  University Press (2017).
-/

open Filter

namespace Constant38a

/-- A **self-avoiding walk** of length $n$ in the square lattice, encoded as an injective path
$p : \{0, \ldots, n\} \to \mathbb{Z}^2$ starting at the origin whose consecutive points are
nearest neighbours. -/
def IsSAW (n : ℕ) (p : Fin (n + 1) → ℤ × ℤ) : Prop :=
  p 0 = 0 ∧ Function.Injective p ∧
    ∀ i : Fin n, |(p i.succ).1 - (p i.castSucc).1| + |(p i.succ).2 - (p i.castSucc).2| = 1

/-- The number $c_n$ of self-avoiding walks of length $n$ starting at the origin. -/
noncomputable def sawCount (n : ℕ) : ℕ := Nat.card {p : Fin (n + 1) → ℤ × ℤ // IsSAW n p}

/-- **Tao's Optimization constant 38a / The square-lattice self-avoiding walk connective
constant**: $\mu_{\mathbb{Z}^2} = \lim_n c_n^{1/n}$. We take a `limsup`; for the square lattice
the limit is known to exist by submultiplicativity. -/
@[optimization_constant "38a"]
noncomputable def C38a : ℝ := limsup (fun n : ℕ => (sawCount n : ℝ) ^ ((n : ℝ)⁻¹)) atTop

/-- The best known lower bound $2.625622$, attributed to Jensen [Jen2004] and reported
in [FV2017]. Conway-Guttmann [CG1993] gave $2.62002$. -/
@[category research solved, AMS 5 82]
theorem c38a_lower_bound : 2.625622 ≤ C38a := by
  sorry

/-- The best known upper bound $2.679193$, attributed to Pönitz-Tittmann [PT2000] and reported
in [FV2017]. -/
@[category research solved, AMS 5 82]
theorem c38a_upper_bound : C38a ≤ 2.679193 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 5 82]
theorem mem_Ico_c38a : answer(sorry) ∈ Set.Ico C38a 2.679193 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 5 82]
theorem mem_Ioc_c38a : answer(sorry) ∈ Set.Ioc 2.625622 C38a := by
  sorry

/-- What is the exact value of the constant? Numerically it is about $2.63815853$, but no exact
value is known. -/
@[category research open, AMS 5 82]
theorem c38a_eq : C38a = answer(sorry) := by
  sorry

end Constant38a
