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
# Tao's Optimization constant 49a / The Erdős-Szemerédi 3-sunflower-free capacity

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 49a](https://teorth.github.io/optimizationproblems/constants/49a.html)
- [DEGKM1997] Deuber, W. A.; Erdős, P.; Gunderson, D. S.; Kostochka, A. V.; Meyer, A. G. "Intersection
  statements for systems of sets." Journal of Combinatorial Theory Series A 79 (1997), 118–132.
- [NS2017] Naslund, E.; Sawin, W. "Upper bounds for sunflower-free sets." Forum of Mathematics
  Sigma 5 (2017), e15. [arXiv:1606.09575](https://arxiv.org/abs/1606.09575)
-/

open Filter Finset

namespace Constant49a

/-- A family of sets is **sunflower-free** if it contains no three distinct members
$A, B, C$ with $A \cap B = A \cap C = B \cap C$. -/
def IsSunflowerFree {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ¬ ∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C

/-- The maximum size of a sunflower-free family of subsets of $\{1, \ldots, n\}$. -/
noncomputable def sunflowerFreeCard (n : ℕ) : ℕ :=
  sSup {#F | (F : Finset (Finset (Fin n))) (_ : IsSunflowerFree F)}

/-- **Tao's Optimization constant 49a / The Erdős-Szemerédi 3-sunflower-free capacity**:
$\lim_n f(n)^{1/n}$, where $f(n)$ is the maximum size of a sunflower-free family of subsets of
$\{1, \ldots, n\}$. We take a `limsup`; a tensor power argument shows it is in fact a limit. -/
@[optimization_constant "49a"]
noncomputable def C49a : ℝ :=
  limsup (fun n : ℕ => (sunflowerFreeCard n : ℝ) ^ ((n : ℝ)⁻¹)) atTop

/-- Trivial lower bound. $f(n)\ge 1$. -/
@[category research solved, AMS 5]
theorem c49a_lower_bound_trivial : 1 ≤ C49a := by
  sorry

/-- Lower bound from [DEGKM1997] (1997). This lower bound is obtained from a construction of
Deuber--Erdős--Gunderson--Kostochka--Meyer. The numerical value is stated in [FPP2024], [TZ2025]. -/
@[category research solved, AMS 5]
theorem c49a_lower_bound_degkm1997 : 1.551 < C49a := by
  sorry

/-- Lower bound from [NS2017] (2017). The arXiv preprint version of [NS2017] records $\mu^{\mathrm
S}\_3\ge 1.554$, citing an unpublished manuscript of the first author. -/
@[category research solved, AMS 5]
theorem c49a_lower_bound_ns2017 : 1.554 ≤ C49a := by
  sorry

/-- Trivial upper bound. $f(n)\le 2^n$. -/
@[category research solved, AMS 5]
theorem c49a_upper_bound_trivial : C49a ≤ 2 := by
  sorry

/-- Upper bound from [NS2017] (2017). They prove $\lvert\mathcal{F}\rvert \le 3(n+1)
\sum\_{k=0}^{\lfloor n/3\rfloor} \binom{n}{k} \le \left(\frac{3}{2^{2/3}}\right)^{n(1+o(1))}$ for
sunflower-free $\mathcal{F}\subseteq 2^{[n]}$. -/
@[category research solved, AMS 5]
theorem c49a_upper_bound_ns2017 : C49a ≤ 3 / (2 ^ (2 / 3 : ℝ)) := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5]
theorem c49a_eq : answer(sorry) = C49a := by
  sorry

end Constant49a
