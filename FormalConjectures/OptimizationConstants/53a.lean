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

/-- Lower bound from [GG2006] (2006). Using $d(C_n^3)\ge d^\*(C_n^3)=3(n-1)$ and $D(G)=1+d(G)$ gives
$D(C_n^3)\ge 3(n-1)+1$, hence $C_{53}\ge 3$. [GG2006-d-ge-dstar] [GG2006-D-equals-1-plus-d]
[GG2006-def-dstar] -/
@[category research solved, AMS 11 20]
theorem c53a_lower_bound_gg2006 : 3 ≤ C53a := by
  sorry

/-- Upper bound from [Grinsztajn2026] (2026). From the pointwise estimate $D(C_n^3)\le 4n-P(n)-2$,
where $P(n)=\max_{p^a\parallel n}p^a$. Since $P(n)\ge2$, this gives $C_{53}\le4$. -/
@[category research solved, AMS 11 20]
theorem c53a_upper_bound_grinsztajn2026 : C53a ≤ 4 := by
  sorry

/-- Upper bound from [Zak2019] (1910). From Corollary 3.11: $D(C_n^3)\le 20369(n-1)+1$ for all $n\ge
2$, hence $C_{53}\le 20369$. [Zak2019-cor3.11] -/
@[category research solved, AMS 11 20]
theorem c53a_upper_bound_zak2019 : C53a ≤ 20369 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11 20]
theorem c53a_eq : answer(sorry) = C53a := by
  sorry

end Constant53a
