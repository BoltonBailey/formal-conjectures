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
import FormalConjectures.ErdosProblems.«36»

/-!
# Tao's Optimization constant 1b / The Erdős minimum overlap constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 1b](https://teorth.github.io/optimizationproblems/constants/1b.html)
- [E1955] Erdős, P. "Problems and results in additive number theory." Colloque sur la Théorie des
  Nombres, Bruxelles, 1955, 127–137 (1956).
- [H2016] Haugland, J. K. "The minimum overlap problem revisited."
  [arXiv:1609.08000](https://arxiv.org/abs/1609.08000)
- [W2022] White, E. P. "Erdős' minimum overlap problem."
  [arXiv:2201.05704](https://arxiv.org/abs/2201.05704)
- [S1958] Swierczkowski, S., On the intersection of a linear set with the translation of its
  complement. Colloq. Math. 5 (1958), 185-197.
- [M1959] Moser, L., On the minimum overlap problem of Erdos, Acta Arith. 5 (1959), 117-119.
- [MRS1956] Motzkin, T. S.; Ralston, K. E.; Selfridge, J. L., Minimal overlap under translation.
  Abstract Bull. Amer. Math. Soc. 62, 558 (1956).
- [H1996] Haugland, J. K., Advances in the minimum overlap problem. J. Number Theory 58 (1996), no.
  1, 71-78.
- [GGSWT2025] Georgiev, Bogdan; Gómez-Serrano, Javier; Tao, Terence; Wagner, Adam Zsolt.
  Mathematical exploration and discovery at scale.
  [arXiv:2511.02864](https://arxiv.org/abs/2511.02864)
- [YKLBMWKCZGS2026] Yuksekgonul, Mert; Koceja, Daniel; Li, Xinhao; Bianchi, Federico; McCaleb, Jed;
  Wang, Xiaolong; Kautz, Jan; Choi, Yejin; Zou, James; Guestrin, Carlos; Sun, Yu. [Learning to
  Discover at Test Time](https://test-time-training.github.io/discover.pdf), 2026.
- [T2026] Together AI. Einsteinarena-new-sota: State-of-the-art results on open math problems, 2026.
  URL https://github.com/togethercomputer/EinsteinArena-new-SOTA.
- [YLTLYSTYLLGDHZSWZSHMELCZX2026] Haotian Ye, Haowei Lin, Jingyi Tang, Yizhen Luo, Caiyin Yang,
  Chang Su, Rahul Thapa, Rui Yang, Ruihua Liu, Zeyu Li, Chong Gao, Dachao Ding, Guangrong He,
  Miaolei Zhang, Lina Sun, Wenyang Wang, Yuchen Zhong, Zhuohao Shen, Di He, Jianzhu Ma, Stefano
  Ermon, Tongyang Li, Xiaowen Chu, James Zou, Yuzhi Xu, Evaluation-driven Scaling for Scientific
  Discovery, https://arxiv.org/abs/2604.19341

The teorth database states the constant in its equivalent continuous form, as the largest $C$
with $\sup_{x \in [-2, 2]} \int_{-1}^1 f(t)g(x + t)\,dt \ge C$ for all non-negative
$f, g : [-1, 1] \to [0, 1]$ with $f + g = 1$ and $\int f = 1$. Here we use the original discrete
form, via the counting function `Erdos36.M` of `FormalConjectures.ErdosProblems.«36»`.

A further, currently unpublished, upper bound of $0.380868$ was announced in 2026.
-/

open Filter

namespace Constant1b

/-- **Tao's Optimization constant 1b / The Erdős minimum overlap constant**:
the limit of $M(n)/n$, where $M(n)$ is the least possible maximum number of representations of
an integer as $a - b$, over all splittings of $\{1, \ldots, 2n\}$ into two sets $A$, $B$ of
equal size. The limit is known to exist; we take a `limsup` so that the definition does not
presuppose this. -/
@[optimization_constant "1b"]
noncomputable def C1b : ℝ := limsup (fun n : ℕ => (Erdos36.M n : ℝ) / n) atTop

/-- Lower bound from [E1955] (1956). -/
@[category research solved, AMS 5 11]
theorem c1b_lower_bound_e1955 : 1 / 4 ≤ C1b := by
  sorry

/-- Lower bound from Scherk (unpublished, 1955). -/
@[category research solved, AMS 5 11]
theorem c1b_lower_bound_scherk : 1 - 1 / Real.sqrt 2 ≤ C1b := by
  sorry

/-- Lower bound from [S1958] (1958). -/
@[category research solved, AMS 5 11]
theorem c1b_lower_bound_s1958 : (4 - Real.sqrt 6) / 5 ≤ C1b := by
  sorry

/-- Lower bound from [M1959] (1959). -/
@[category research solved, AMS 5 11]
theorem c1b_lower_bound_m1959 : Real.sqrt (4 - Real.sqrt 15) ≤ C1b := by
  sorry

/-- Lower bound from [W2022] (2022). -/
@[category research solved, AMS 5 11]
theorem c1b_lower_bound_w2022 : 0.379005 ≤ C1b := by
  sorry

/-- Upper bound from [E1955] (1956). -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound_e1955 : C1b ≤ 1 / 2 := by
  sorry

/-- Upper bound from Erdős (unpublished). -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound_erdos : C1b ≤ 4 / 9 := by
  sorry

/-- Upper bound from [MRS1956] (1956). -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound_mrs1956_1 : C1b ≤ 5 / 12 := by
  sorry

/-- Upper bound from [MRS1956] (1956). -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound_mrs1956_2 : C1b ≤ 0.4 := by
  sorry

/-- Upper bound from Haugland (unpublished, 1993). -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound_haugland : C1b ≤ 0.385694 := by
  sorry

/-- Upper bound from [H1996] (1996). -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound_h1996 : C1b ≤ 0.382002 := by
  sorry

/-- Upper bound from [H2016] (2016). -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound_h2016 : C1b ≤ 0.380927 := by
  sorry

/-- Upper bound from [GGSWT2025] (2025). AlphaEvolve -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound_ggswt2025 : C1b ≤ 0.380924 := by
  sorry

/-- Upper bound from [YKLBMWKCZGS2026] (2026). TTT-Discover -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound_yklbmwkczgs2026 : C1b ≤ 0.380876 := by
  sorry

/-- Upper bound from [T2026] (2026). TogetherAI -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound_t2026 : C1b ≤ 0.380871 := by
  sorry

/-- Upper bound from [YLTLYSTYLLGDHZSWZSHMELCZX2026] (2026). SimpleTES -/
@[category research solved, AMS 5 11]
theorem c1b_upper_bound_yltlystyllgdhzswzshmelczx2026 : C1b ≤ 0.380868 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11]
theorem c1b_eq : answer(sorry) = C1b := by
  sorry

end Constant1b
