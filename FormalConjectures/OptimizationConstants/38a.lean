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
- [SlaBounds] Slade, Gordon. "Bounds on the self-avoiding-walk connective constant." In: Benedetto,
  John J. (ed.), "The Journal of Fourier Analysis and Applications." CRC Press (2020), 525–533. DOI:
  [10.1201/9780429332838-32](https://doi.org/10.1201/9780429332838-32). [Author
  PDF](https://personal.math.ubc.ca/~slade/kahane.pdf).
- [Num2026] Numaro ([numaro.tech](https://numaro.tech)). "An improved rigorous lower bound for the
  square-lattice SAW connective constant." [Certificate
  archive](https://doi.org/10.5281/zenodo.21546041), submitted to this repository (2026).
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

/-- Trivial lower bound. From the general bound $d \le \mu \le 2d-1$ with $d=2$. [SlaBounds-simple]
-/
@[category research solved, AMS 5 82]
theorem c38a_lower_bound_trivial : 2 ≤ C38a := by
  sorry

/-- Lower bound from [SlaBounds] (2020). Reported (Table 1) as the best rigorous lower bound for
$d=2$ in this survey; the survey attributes it to [CG1993]. [SlaBounds-table1-d2]
[SlaBounds-conway-guttmann] -/
@[category research solved, AMS 5 82]
theorem c38a_lower_bound_slabounds : 2.62002 ≤ C38a := by
  sorry

/-- Lower bound from [FV2017] (2017). Reported as a rigorous lower bound in [FV2017] (attributed
there to [Jen2004-lb]). [FV2017-bounds-square] [FV2017-ref-182] -/
@[category research solved, AMS 5 82]
theorem c38a_lower_bound_fv2017 : 2.625622 ≤ C38a := by
  sorry

/-- Lower bound from [Num2026] (2026). Kesten irreducible-bridge renewal exactly as in [Jen2004-lb],
extended two span levels past the 2004 computation (span $L=17$, series length $N=260$) by an exact
cell-by-cell finite-lattice transfer matrix (CRT big-integer arithmetic); the certificate is a
single exact big-integer inequality (self-contained checker included), and secondary certificates at
Jensen's own span ($L=15$, $N=260$ gives $2.6256270$) and at $L=16$ ($2.6265705$) independently also
exceed $2.625622$. [Num2026-bound] -/
@[category research solved, AMS 5 82]
theorem c38a_lower_bound_num2026 : 2.6273856 ≤ C38a := by
  sorry

/-- Trivial upper bound. From the general bound $d \le \mu \le 2d-1$ with $d=2$. [SlaBounds-simple]
-/
@[category research solved, AMS 5 82]
theorem c38a_upper_bound_trivial : C38a ≤ 3 := by
  sorry

/-- Upper bound from [SlaBounds] (2020). Reported (Table 1) as the best rigorous upper bound for
$d=2$ in this survey, attributed there to [Alm1993]. [SlaBounds-table1-d2] -/
@[category research solved, AMS 5 82]
theorem c38a_upper_bound_slabounds : C38a ≤ 2.69576 := by
  sorry

/-- Upper bound from [FV2017] (2017). Reported as a rigorous upper bound in [FV2017] (attributed
there to [PT2000]). [FV2017-bounds-square] [FV2017-ref-277] -/
@[category research solved, AMS 5 82]
theorem c38a_upper_bound_fv2017 : C38a ≤ 2.679193 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 82]
theorem c38a_eq : answer(sorry) = C38a := by
  sorry

end Constant38a
