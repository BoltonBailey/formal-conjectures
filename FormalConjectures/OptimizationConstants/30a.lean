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
# Tao's Optimization constant 30a / The Stanley-Wilf limit for the pattern 1324

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 30a](https://teorth.github.io/optimizationproblems/constants/30a.html)
- [B04] Bóna, M. "The limit of a Stanley-Wilf sequence is not always rational, and layered
  patterns beat monotone patterns." Journal of Combinatorial Theory Series A 110 (2005), 223–235.
- [CJS12] Claesson, A.; Jelínek, V.; Steingrímsson, E. "Upper bounds for the Stanley-Wilf limit
  of 1324 and other layered patterns." Journal of Combinatorial Theory Series A 119 (2012),
  1680–1691.
- [BBEPP2017] Bevan, D.; Brignall, R.; Elvey Price, A.; Pantone, J. "A structural
  characterisation of $\mathrm{Av}(1324)$ and new bounds on its growth rate." European Journal of
  Combinatorics 88 (2020), 103115. [arXiv:1711.10325](https://arxiv.org/abs/1711.10325)
- [B05] Bóna, Miklós. "The limit of a Stanley–Wilf sequence is not always rational, and layered
  patterns beat monotone patterns." J. Combin. Theory Ser. A 110 (2005), no. 2, 223–235. DOI:
  [10.1016/j.jcta.2004.07.014](https://doi.org/10.1016/j.jcta.2004.07.014). [arXiv
  PDF](https://arxiv.org/pdf/math/0403502.pdf)
- [AERWZ] Albert, M. H.; Elder, M.; Rechnitzer, A.; Westcott, P.; Zabrocki, M. "On the Stanley–Wilf
  limit of 4231-avoiding permutations and a conjecture of Arratia." Adv. Appl. Math. 36 (2006), no.
  2, 96–105. DOI: [10.1016/j.aam.2005.05.007](https://doi.org/10.1016/j.aam.2005.05.007). [arXiv
  PDF](https://arxiv.org/pdf/math/0502504.pdf)
- [Bev] Bevan, David. "Permutations avoiding 1324 and patterns in Łukasiewicz paths." J. London
  Math. Soc. 92 (2015), no. 1, 105–122. DOI:
  [10.1112/jlms/jdv020](https://doi.org/10.1112/jlms/jdv020). [arXiv
  PDF](https://arxiv.org/pdf/1406.2890.pdf)
- [B14a] Bóna, Miklós. "A new upper bound for 1324-avoiding permutations." Combinatorics,
  Probability and Computing 23 (2014), no. 5, 717–724. DOI:
  [10.1017/S0963548314000091](https://doi.org/10.1017/S0963548314000091). [arXiv
  PDF](https://arxiv.org/pdf/1207.2379.pdf)
- [B14b] Bóna, Miklós. "A new record for 1324-avoiding permutations." European J. Math. 1 (2015),
  no. 1, 198–206. DOI: [10.1007/s40879-014-0020-6](https://doi.org/10.1007/s40879-014-0020-6).
  [arXiv PDF](https://arxiv.org/pdf/1404.4033.pdf)
-/

open Filter

namespace Constant30a

/-- The pattern $1324$, as an order-defining function on four points. -/
def pattern1324 : Fin 4 → Fin 4 := ![0, 2, 1, 3]

/-- A permutation of $\{1, \ldots, n\}$ **avoids** the pattern $1324$ if there are no indices
$i_1 < i_2 < i_3 < i_4$ on which it is order-isomorphic to $1324$. -/
def Avoids1324 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ¬ ∃ f : Fin 4 → Fin n, StrictMono f ∧
    ∀ a b : Fin 4, pattern1324 a < pattern1324 b ↔ σ (f a) < σ (f b)

/-- $S_n(1324)$, the number of permutations of $\{1, \ldots, n\}$ avoiding the pattern
$1324$. -/
noncomputable def S (n : ℕ) : ℕ := Nat.card {σ : Equiv.Perm (Fin n) // Avoids1324 σ}

/-- **Tao's Optimization constant 30a / The Stanley-Wilf limit for the pattern 1324**:
$\lim_n S_n(1324)^{1/n}$. The limit is known to exist by Marcus-Tardos and Arratia; we take a
`limsup` so that the definition does not presuppose this. -/
@[optimization_constant "30a"]
noncomputable def C30a : ℝ := limsup (fun n : ℕ => (S n : ℝ) ^ ((n : ℝ)⁻¹)) atTop

/-- Lower bound from [B05] (2004). Lower bound recorded in Table 1 of BBEPP2017. [BBEPP2017-t1-lb-9]
-/
@[category research solved, AMS 5]
theorem c30a_lower_bound_b05 : 9 ≤ C30a := by
  sorry

/-- Lower bound from [AERWZ] (2005). Lower bound recorded in Table 1 of BBEPP2017.
[BBEPP2017-t1-lb-9.47] -/
@[category research solved, AMS 5]
theorem c30a_lower_bound_aerwz : 9.47 ≤ C30a := by
  sorry

/-- Lower bound from [Bev] (2015). Lower bound recorded in Table 1 of BBEPP2017.
[BBEPP2017-t1-lb-9.81] -/
@[category research solved, AMS 5]
theorem c30a_lower_bound_bev : 9.81 ≤ C30a := by
  sorry

/-- Lower bound from [BBEPP2017] (2019). Current best rigorous lower bound. [BBEPP2017-t1-thiswork]
-/
@[category research solved, AMS 5]
theorem c30a_lower_bound_bbepp2017 : 10.27 ≤ C30a := by
  sorry

/-- Upper bound from [B04] (2003). Upper bound recorded in Table 1 of [BBEPP2017].
[BBEPP2017-t1-ub-288] -/
@[category research solved, AMS 5]
theorem c30a_upper_bound_b04 : C30a ≤ 288 := by
  sorry

/-- Upper bound from [CJS12] (2012). Upper bound recorded in Table 1 of [BBEPP2017].
[BBEPP2017-t1-ub-16] -/
@[category research solved, AMS 5]
theorem c30a_upper_bound_cjs12 : C30a ≤ 16 := by
  sorry

/-- Upper bound from [B14a] (2014). Upper bound recorded in Table 1 of [BBEPP2017].
[BBEPP2017-t1-ub-13.93] -/
@[category research solved, AMS 5]
theorem c30a_upper_bound_b14a : C30a ≤ 13.93 := by
  sorry

/-- Upper bound from [B14b] (2015). Upper bound recorded in Table 1 of [BBEPP2017].
[BBEPP2017-t1-ub-13.74] -/
@[category research solved, AMS 5]
theorem c30a_upper_bound_b14b : C30a ≤ 13.74 := by
  sorry

/-- Upper bound from [BBEPP2017] (2019). Current best rigorous upper bound. [BBEPP2017-t1-thiswork]
-/
@[category research solved, AMS 5]
theorem c30a_upper_bound_bbepp2017 : C30a ≤ 13.5 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5]
theorem c30a_eq : answer(sorry) = C30a := by
  sorry

end Constant30a
