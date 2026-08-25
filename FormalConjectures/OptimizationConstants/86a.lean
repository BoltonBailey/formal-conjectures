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
# Tao's Optimization constant 86a / The Schur-Siegel-Smyth trace constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 86a](https://teorth.github.io/optimizationproblems/constants/86a.html)
- [Sch18] Schur, I. "Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit
  ganzzahligen Koeffizienten." Mathematische Zeitschrift 1 (1918), 377–402.
- [Smy84] Smyth, C. J. "The mean values of totally real algebraic integers." Mathematics of
  Computation 42 (1984), 663–681.
- [Smi24] Smith, A. "Algebraic integers with conjugates in a prescribed distribution." Annals of
  Mathematics 200 (2024), 249–299.
- [SO24] Serre-type explicit measures optimised by gradient descent, 2024.
- [OSS25] Orloski, A.; Sardari, N. T.; Smith, A. Logarithmic-energy constraints in Smyth's
  linear program, 2025.
- [Sie45] Siegel, C. L. "The trace of totally positive and real algebraic integers." Annals of
  Mathematics 46 (1945), 302–312. DOI: [10.2307/1969025](https://doi.org/10.2307/1969025).
- [FGR99] Flammang, V.; Grandcolas, M.; Rhin, G. "Small Salem numbers." In: "Number Theory in
  Progress", Vol. 1 (Zakopane-Kościelisko, 1997), de Gruyter, Berlin, 1999, pp. 165–168. Note that
  the stated subject of this note is the computation of all Salem numbers $< 1.3$ of degree $\le
  40$; the trace bound $1.7735$ is attributed to it by [Fla19] and [OSS25] and is presumably
  obtained there as an auxiliary result.
- [MS04] McKee, J.; Smyth, C. J. "Salem numbers of trace $-2$ and traces of totally positive
  algebraic integers." In: "Algorithmic Number Theory (ANTS-VI)", Lecture Notes in Computer Science
  3076, Springer, 2004, pp. 327–337. DOI:
  [10.1007/978-3-540-24847-7\_25](https://doi.org/10.1007/978-3-540-24847-7_25).
- [ABP06] Aguirre, J.; Bilbao, M.; Peral, J. C. "The trace of totally positive algebraic integers."
  Mathematics of Computation 75 (2006), no. 253, 385–393. DOI:
  [10.1090/S0025-5718-05-01776-X](https://doi.org/10.1090/S0025-5718-05-01776-X).
- [AP07] Aguirre, J.; Peral, J. C. "The integer Chebyshev constant of Farey intervals." Publicacions
  Matemàtiques 51 (2007), Proceedings of the Primeras Jornadas de Teoría de Números, 11–27. DOI:
  [10.5565/publmat\_pjtn05\_01](https://doi.org/10.5565/publmat_pjtn05_01).
- [AP08] Aguirre, J.; Peral, J. C. "The trace problem for totally positive algebraic integers." With
  an appendix by Jean-Pierre Serre. In: "Number Theory and Polynomials", London Mathematical Society
  Lecture Note Series 352, Cambridge University Press, 2008, pp. 1–19. DOI:
  [10.1017/CBO9780511721274.003](https://doi.org/10.1017/CBO9780511721274.003).
- [Fla09] Flammang, V. "Trace of totally positive algebraic integers and integer transfinite
  diameter." Mathematics of Computation 78 (2009), no. 266, 1119–1125. DOI:
  [10.1090/S0025-5718-08-02120-0](https://doi.org/10.1090/S0025-5718-08-02120-0).
- [McK11] McKee, J. "Computing totally positive algebraic integers of small trace." Mathematics of
  Computation 80 (2011), no. 274, 1041–1052. DOI:
  [10.1090/S0025-5718-2010-02424-X](https://doi.org/10.1090/S0025-5718-2010-02424-X).
- [LW11] Liang, Y.; Wu, Q. "The trace problem for totally positive algebraic integers." Journal of
  the Australian Mathematical Society 90 (2011), no. 3, 341–354. DOI:
  [10.1017/S1446788711001030](https://doi.org/10.1017/S1446788711001030).
- [Fla16] Flammang, V. "Une nouvelle minoration pour la trace absolue des entiers algébriques
  totalement positifs." Preprint (2016), HAL: [hal-01346165](https://hal.science/hal-01346165). The
  same title and result were posted as [arXiv:1907.09407](https://arxiv.org/abs/1907.09407) (2019);
  [OSS25] cite the arXiv posting under the key [Fla19] while dating the result to 2016.
- [WWW21] Wang, C.; Wu, J.; Wu, Q. "Totally positive algebraic integers with small trace."
  Mathematics of Computation 90 (2021), no. 331, 2317–2332. DOI:
  [10.1090/mcom/3636](https://doi.org/10.1090/mcom/3636).
-/

open Polynomial

namespace Constant86a

/-- A monic integer polynomial is the minimal polynomial of a **totally positive** algebraic
integer exactly when it is irreducible of positive degree and all of its complex roots are real
and strictly positive. -/
def IsTotallyPositive (f : ℤ[X]) : Prop :=
  f.Monic ∧ Irreducible f ∧ 0 < f.natDegree ∧
    ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, z.im = 0 ∧ 0 < z.re

/-- The **absolute trace** (trace-to-degree ratio) of the algebraic integer with minimal
polynomial $f$ of degree $d$, namely $-a_{d-1}/d$. -/
noncomputable def absTrace (f : ℤ[X]) : ℝ :=
  -(f.coeff (f.natDegree - 1) : ℝ) / f.natDegree

/-- **Tao's Optimization constant 86a / The Schur-Siegel-Smyth trace constant**:
the smallest limit point of the absolute traces of totally positive algebraic integers,
equivalently the supremum of the $\rho \ge 0$ for which all but finitely many totally positive
algebraic integers $\alpha$ satisfy $\mathrm{tr}(\alpha) \ge \rho \deg(\alpha)$. -/
@[optimization_constant "86a"]
noncomputable def C86a : ℝ :=
  sSup {ρ : ℝ | 0 ≤ ρ ∧ {f : ℤ[X] | IsTotallyPositive f ∧ absTrace f < ρ}.Finite}

/-- Trivial lower bound. By AM–GM, $\overline{\mathrm{tr}}(\alpha) \ge \lvert N(\alpha)\rvert^{1/d}
\ge 1$, since the norm of a nonzero algebraic integer is a nonzero rational integer. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_trivial : 1 ≤ C86a := by
  sorry

/-- Lower bound from [Sch18] (1918). Schur, via the arithmetic–geometric mean inequality applied to
the discriminant. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_sch18 : Real.sqrt (Real.exp 1) ≤ C86a := by
  sorry

/-- Lower bound from [Sie45] (1945). The website lists this value as approximate ($\approx
1.73361$). Siegel; the bound is $e(1+\nu^{-1})^{-\nu}$ for a root $\nu$ of a transcendental
equation. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_sie45 : 1.73361 ≤ C86a := by
  sorry

/-- Lower bound from [Smy84] (1984). Smyth's **auxiliary function method**: if $x - \sum\_Q c\_Q
\log\lvert Q(x)\rvert \ge c$ for all $x > 0$, with $c\_Q > 0$ and $Q$ ranging over a finite set of
integer polynomials, then $\overline{\mathrm{tr}}(\alpha) \ge c$ for all but finitely many $\alpha$.
Every subsequent entry in this table refines the choice and optimization of the $Q$ and $c\_Q$. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_smy84 : 1.7719 ≤ C86a := by
  sorry

/-- Lower bound from [FGR99] (1999). Dated 1997 in [Fla19] and [OSS25] (the conference volume
appeared in 1999). See the note on this reference below. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_fgr99 : 1.7735 ≤ C86a := by
  sorry

/-- Lower bound from [MS04] (2004). Value as reported in [Fla19]; rounded to $1.7783$ in the
historical table of [OSS25]. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_ms04 : 1.7783786 ≤ C86a := by
  sorry

/-- Lower bound from [ABP06] (2006). -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_abp06 : 1.78002 ≤ C86a := by
  sorry

/-- Lower bound from [AP07] (2007). -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_ap07 : 1.7836 ≤ C86a := by
  sorry

/-- Lower bound from [AP08] (2008). Value as reported in [Fla19]; rounded to $1.7841$ in [OSS25].
This paper also carries Serre's appendix; see "Additional comments and links" below. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_ap08 : 1.784109 ≤ C86a := by
  sorry

/-- Lower bound from [Fla09] (2009). Introduces the *recursive algorithm*: the auxiliary polynomials
are generated inductively via LLL rather than found heuristically, building on the link between
auxiliary functions and the integer transfinite diameter established in [Wu03]. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_fla09 : 1.78702 ≤ C86a := by
  sorry

/-- Lower bound from [McK11] (2010). First to use auxiliary polynomials with complex roots. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_mck11 : 1.78839 ≤ C86a := by
  sorry

/-- Lower bound from [LW11] (2011). Value as reported in [Fla19]; rounded to $1.7919$ in [OSS25]. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_lw11 : 1.79193 ≤ C86a := by
  sorry

/-- Lower bound from [Fla16] (2016). A variant in the use of the recursive algorithm of [Fla09].
Holds unless the minimal polynomial of $\alpha$ is one of $x-1$, $x^2-3x+1$, $x^3-5x^2+6x-1$,
$x^4-7x^3+13x^2-7x+1$, $x^4-7x^3+14x^2-8x+1$. Rounded to $1.7928$ and dated 2016 in the historical
table of [OSS25], which cites the later arXiv posting. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_fla16 : 1.792812 ≤ C86a := by
  sorry

/-- Lower bound from [WWW21] (2021). Rounded to $1.7931$ in the historical table of [OSS25]; the
value $1.793145$ is as reported in [Fla24]. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_www21 : 1.793145 ≤ C86a := by
  sorry

/-- Lower bound from [OSS25] (2005). Adds constraints coming from the logarithmic energy of the
limiting measure to Smyth's linear program, sharply reducing the number of variables required. The
authors prove existence and uniqueness of an optimal solution, characterize it in terms of
polynomials, and solve numerically by gradient descent. Schur's and Siegel's bounds are recovered as
the two simplest cases. -/
@[category research solved, AMS 11 12]
theorem c86a_lower_bound_oss25 : 1.80203 ≤ C86a := by
  sorry

/-- Upper bound from Classical. For $n \ge 3$ the totally positive algebraic integer $\alpha\_n =
4\cos^2(\pi/n) = 2 + 2\cos(2\pi/n)$ has degree $\varphi(n)/2$ and $\overline{\mathrm{tr}}(\alpha\_n)
= 2 + 2\mu(n)/\varphi(n)$, which is $< 2$ for $n$ prime and tends to $2$. Corresponds to the trivial
case $\Lambda\_\emptyset = 2$ in the framework of [SO24]. -/
@[category research solved, AMS 11 12]
theorem c86a_upper_bound_classical : C86a ≤ 2 := by
  sorry

/-- Upper bound from [Smi24] (2024). "There are infinitely many totally positive algebraic integers
$\alpha$ with $\mathrm{tr}(\alpha) < 1.89831 \cdot \deg(\alpha)$." Obtained by combining Serre's
measure $\nu\_S$ (appendix to [AP08]) with Smith's converse to Fekete's theorem, which shows that
the necessary conditions on a limiting distribution of conjugates are also sufficient. This is the
result that **disproves the conjecture $C\_{86} = 2$**. Stated as $C\_{86} \le 1.898304$ in [SO24].
-/
@[category research solved, AMS 11 12]
theorem c86a_upper_bound_smi24 : C86a ≤ 1.89831 := by
  sorry

/-- Upper bound from [SO24] (2024). Explicit measures satisfying the conditions of [Smi24],
optimized by gradient descent. Corollary 1.10 of [SO24] gives $\lvert \Lambda\_A - 1.8215998 \rvert
\le 10^{-7}$ for $A = \{x,\ 1-x,\ x^2-3x+1,\ x^3-5x^2+6x-1\}$, and $C\_{86} \le \Lambda\_A$.
Intermediate values in the same family: $\Lambda\_{\{x\}} \approx 1.898302$ (Serre's constant), then
$1.84701204$ and $1.8224798$. Preprint; not listed as journal-published as of this writing. -/
@[category research solved, AMS 11 12]
theorem c86a_upper_bound_so24 : C86a ≤ 1.8216 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11 12]
theorem c86a_eq : answer(sorry) = C86a := by
  sorry

end Constant86a
