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
import FormalConjectures.ErdosProblems.«90»

/-!
# Tao's Optimization constant 84a / The Erdős unit distance exponent

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 84a](https://teorth.github.io/optimizationproblems/constants/84a.html)
- [E1946] Erdős, P. "On sets of distances of $n$ points." American Mathematical Monthly 53 (1946),
  248–250.
- [SST1984] Spencer, J.; Szemerédi, E.; Trotter, W. T. "Unit distances in the Euclidean plane."
  Graph Theory and Combinatorics (1984), 293–303.
- [S2026] Sawin, W. "An explicit lower bound for the unit distance problem."
  [arXiv:2605.20579](https://arxiv.org/abs/2605.20579)
- [ABGLSSTWW2026] Alon, N.; Bloom, T. F.; Gowers, W. T.; Litt, D.; Sawin, W.; Shankar, A.;
  Tsimerman, J.; Wang, V.; Matchett Wood, M. "Remarks on the disproof of the unit distance
  conjecture." [arXiv:2605.20695](https://arxiv.org/abs/2605.20695)
- [O2026] OpenAI. "An OpenAI model has disproved a central conjecture in discrete geometry". Blog
  post, 20 May 2026.
  [openai.com/index/model-disproves-discrete-geometry-conjecture](https://openai.com/index/model-disproves-discrete-geometry-conjecture/).
- [EPF90] Bloom, Thomas F. (ed.). "Erdős Problem #90: Discussion thread".
  [erdosproblems.com/forum/thread/90](https://www.erdosproblems.com/forum/thread/90) (accessed 22
  May 2026).
- [MO511514] "What is the unit distance exponent?" MathOverflow question 511514,
  [mathoverflow.net/q/511514](https://mathoverflow.net/q/511514) (accessed 22 May 2026).

The underlying counting function is formalised in `FormalConjectures.ErdosProblems.«90»` as
`Erdos90.maxUnitDistances`.
-/

open Filter

namespace Constant84a

/-- **Tao's Optimization constant 84a / The Erdős unit distance exponent**:
the exponent $\limsup_{n \to \infty} \frac{\log u(n)}{\log n}$, where $u(n)$ is the maximum
number of unit distances determined by $n$ points in the plane. -/
@[optimization_constant "84a"]
noncomputable def C84a : ℝ :=
  limsup (fun n : ℕ => Real.log (Erdos90.maxUnitDistances n) / Real.log n) atTop

/-- Lower bound from [E1946] (1946). A $\sqrt{n} \times \sqrt{n}$ portion of the integer lattice
gives $u(n) \gg n^{1 + c/\log\log n}$, hence $\limsup \log u(n)/\log n \geq 1$. Conjectured by Erdős
to be sharp. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_e1946 : 1 ≤ C84a := by
  sorry

/-- Lower bound from [O2026], [ABGLSSTWW2026] (2026). An OpenAI internal reasoning model produced a
(one-shot) construction giving $u(n) \gg n^{1+\varepsilon}$ for some $\varepsilon > 0$ and
infinitely many $n$, disproving Erdős' conjecture. The construction is number-theoretic, using
algebraic number fields of large degree and small discriminant via a Golod–Shafarevich argument. A
particular parameter choice in [ABGLSSTWW2026] yields the explicit value $\varepsilon \approx 6.24
\cdot 10^{-38}$. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_o2026_abglsstww2026 : 1 < C84a := by
  sorry

/-- Lower bound from [S2026] (2026). Sawin, by optimizing the Golod–Shafarevich step and the choice
of number field. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_s2026 : 1.014 ≤ C84a := by
  sorry

/-- Lower bound from [EPF90] (2026). mlewko, posted on the Erdős Problems forum (21 May 2026);
reuses Sawin's argument with optimized finite data ($\lvert T\rvert = 74$, $\lvert S\rvert = 1082$)
produced by ChatGPT 5.5 Pro. Unverified. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_epf90 : 1.03184 ≤ C84a := by
  sorry

/-- Lower bound from [MO511514] (2026). spiderduckpig, posted on MathOverflow (21 May 2026);
replaces the primes $347,353$ in mlewko's $T$ by $503,601$. Unverified. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_mo511514_1 : 1.03188 ≤ C84a := by
  sorry

/-- Lower bound from [MO511514] (2026). spiderduckpig, MathOverflow comment (22 May 2026); further
replaces $337,349,373$ in $T$ by $389,443,587$. Unverified. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_mo511514_2 : 1.03190 ≤ C84a := by
  sorry

/-- Lower bound from [MO511514] (2026). spiderduckpig, MathOverflow comment (22 May 2026); claimed
via a weighted-Zassenhaus-filtration modification of Sawin's Lemma 11, so requires a change to the
proof structure and not just finite data. Unverified. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_mo511514_3 : 1.0333487 ≤ C84a := by
  sorry

/-- Lower bound from [MO511514] (2026). Naslund, MathOverflow answer (22 May 2026); combines
spiderduckpig's Golod–Shafarevich refinement with three further structural improvements to Sawin's
argument — a Louboutin-style bound on $L(1,\chi)$ via $\zeta\_{E_T}$, a sphere-overlap refinement of
Lemmas 4–5, and a narrow-class-group sharpening of Lemma 7 — then re-optimizes $T$ (the first $51$
odd primes minus $\{227,233\}$). Hybrid ChatGPT 5.5 Pro / human work. Unverified. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_mo511514_4 : 1.03447 ≤ C84a := by
  sorry

/-- Lower bound from [MO511514] (2026). Naslund, revised (≈24 May 2026); corrects the optimization
to fully include the narrow-class-group improvement, with optimizer $\lvert T\rvert = 48$. (An
intermediate $T$-tweak had given $1.03448\dots$.) Unverified. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_mo511514_5 : 1.0346749 ≤ C84a := by
  sorry

/-- Lower bound from [MO511514] (2026). Tseng, MathOverflow answer (25 May 2026). Does **not**
improve the record exponent, but supplies a reproducible pointwise certificate: $u(n) \geq
\frac{1}{128 P\_{89}} n^{1.03158935}$ for all sufficiently large $n$, where $P\_{89}$ is the product
of the first $89$ odd primes. Uses Sawin's construction as a black box plus prime-ideal
microselection, a fractional-knapsack model and a dyadic-circle covering certificate
([repository](https://github.com/Tseng-math/erdos-unit-distance-pointwise-certificate)).
AI-assisted. Unverified. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_mo511514_6 : 1.03158935 ≤ C84a := by
  sorry

/-- Lower bound from [MO511514] (2026). spiderduckpig, revised answer (25 May 2026); a reproducible
finite-data/certificate improvement. Does **not** exceed Naslund's $1.0346749\dots$. Unverified. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_mo511514_7 : 1.0346609571815997 ≤ C84a := by
  sorry

/-- Lower bound from [MO511514] (2026). Naslund, revised (≈25 May 2026); replaces the sphere-packing
estimate by a covolume bound on the ideal lattice (asserted to be essentially optimal for this part
of the argument), re-optimizing to $\lvert T\rvert = 39$. Hybrid ChatGPT 5.5 Pro / human work.
Current best. Unverified. -/
@[category research solved, AMS 52]
theorem c84a_lower_bound_mo511514_8 : 1.03583 ≤ C84a := by
  sorry

/-- Upper bound from [E1946] (1946). Erdős' original argument, based on the observation that the
unit-distance graph contains no $K\_{2,3}$. -/
@[category research solved, AMS 52]
theorem c84a_upper_bound_e1946 : C84a ≤ 3 / 2 := by
  sorry

/-- Upper bound from [SST1984] (1984). Spencer, Szemerédi and Trotter; via the Szemerédi–Trotter
incidence theorem. -/
@[category research solved, AMS 52]
theorem c84a_upper_bound_sst1984 : C84a ≤ 4 / 3 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 52]
theorem c84a_eq : answer(sorry) = C84a := by
  sorry

end Constant84a
