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
# Tao's Optimization constant 53a / The Davenport constant for $C_n^3$

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 53a](https://teorth.github.io/optimizationproblems/constants/53a.html)
- [GG2006] Gao, W.; Geroldinger, A. "Zero-sum problems in finite abelian groups: a survey."
  Expositiones Mathematicae 24 (2006), 337–369.
- [Zak2019] Zakarczemny, M. Bound $D(C_n^3) \le 20369(n-1) + 1$, 2019.
- [Grinsztajn2026] Pointwise estimate $D(C_n^3) \le 4n - P(n) - 2$, 2026.
-/

namespace Constant53a

/-- The **Davenport constant** of a finite abelian group $G$: the smallest $l$ such that every
sequence over $G$ of length at least $l$ has a non-empty zero-sum subsequence. Sequences are
modelled as multisets, since only the multiset of terms matters. -/
noncomputable def davenport (G : Type*) [AddCommGroup G] [Fintype G] : ℕ :=
  sInf {l : ℕ | ∀ s : Multiset G, l ≤ Multiset.card s → ∃ t ≤ s, t ≠ 0 ∧ t.sum = 0}

/-- **Tao's Optimization constant 53a / The Davenport constant for $C_n^3$**:
$\sup_{n \ge 2} \frac{D(C_n^3) - 1}{n - 1}$, the maximal normalised Davenport constant among the
rank-$3$ groups $C_n^3$. -/
@[optimization_constant "53a"]
noncomputable def C53a : ℝ :=
  ⨆ n : ℕ, ((davenport (Fin 3 → ZMod (n + 2)) : ℝ) - 1) / (n + 1)

/-- The lower bound $3$, which follows from $D(C_n^3) \ge 3(n - 1) + 1$ [GG2006]. -/
@[category research solved, AMS 11 20]
theorem c53a_lower_bound : 3 ≤ C53a := by
  sorry

/-- The best known upper bound $4$, which follows from the pointwise estimate
$D(C_n^3) \le 4n - P(n) - 2$ [Grinsztajn2026], where $P(n)$ is the largest prime power dividing
$n$. The bound $20369$ was previously the best available [Zak2019]. -/
@[category research solved, AMS 11 20]
theorem c53a_upper_bound : C53a ≤ 4 := by
  sorry

/-- How can the upper bound be improved? -/
@[category research open, AMS 11 20]
theorem mem_Ico_c53a : answer(sorry) ∈ Set.Ico C53a 4 := by
  sorry

/-- How can the lower bound be improved? -/
@[category research open, AMS 11 20]
theorem mem_Ioc_c53a : answer(sorry) ∈ Set.Ioc 3 C53a := by
  sorry

/-- What is the exact value of the constant? It is conjectured that
$D(C_n^3) = 3(n - 1) + 1$ for every $n$ [GG2006], which would give the value $3$. -/
@[category research open, AMS 11 20]
theorem c53a_eq : C53a = answer(sorry) := by
  sorry

end Constant53a
