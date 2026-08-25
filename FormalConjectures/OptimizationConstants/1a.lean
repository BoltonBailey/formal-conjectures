/-
Copyright 2025 The Formal Conjectures Authors.

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
# Tao's Optimization constant 1a / An autocorrelation constant related to Sidon sets

*References:*
- [Tao's optimization constant 1a](https://teorth.github.io/optimizationproblems/constants/1a.html)
- [M2010] Matolcsi, Máté, and Carlos Vinuesa. "Improved bounds on the supremum of autoconvolutions."
  Journal of mathematical analysis and applications 372.2 (2010): 439-447. [arXiv:0907.1379](https://arxiv.org/abs/0907.1379)
- [Y2026] Yuksekgonul, Mert et al., "Learning to Discover at Test Time," 2026, [arXiv:2601.16175](https://arxiv.org/abs/2601.16175)
- [MO2004] Martin, Greg; O’Bryant, Kevin. The symmetric subset problem in continuous Ramsey theory.
  Exp. Math. 16, No. 2, 145-165 (2007). [arXiv:math/0410004](https://arxiv.org/abs/math/0410004)
- [MO2009] Martin, Greg; O’Bryant, Kevin. The supremum of autoconvolutions, with applications to
  additive number theory. Ill. J. Math. 53, No. 1, 219-235 (2009).
  [arXiv:0807.5121](https://arxiv.org/abs/0807.5121)
- [MV2009] Matolcsi, Máté; Vinuesa, Carlos. Improved bounds on the supremum of autoconvolutions. J.
  Math. Anal. Appl. 372, No. 2, 439-447 (2010). [arXiv:0907.1379](https://arxiv.org/abs/0907.1379)
- [CS2017] Cloninger, Alexander; Steinerberger, Stefan. On suprema of autoconvolutions with an
  application to Sidon sets. Proc. Amer. Math. Soc. 145, No. 8, 3191–3200 (2017).
  [arXiv:1403.7988](https://arxiv.org/abs/1403.7988)
- [IX2026] Ivanisvili, Paata; Xie, Xinyuan. Grokability in five inequalities. 2026.
  [arXiv:2605.05193](https://arxiv.org/abs/2605.05193)
- [PBV2026] Piterbarg, Andrei; Bajaj, Jai; Vincent, Derrick. A multi-scale arcsine lower bound for
  the Sidon autocorrelation constant $C\_{1a}$, 2026.
  https://github.com/AndreiPiterbarg/sidon-autocorrelation
- [SS2002] Schinzel, A.; Schmidt, W. M.. Comparison of $L^1$ and $L^\infty$ norms of squares of
  polynomials. Acta Arith. 104, No. 3, 283-296 (2002).
- [GGSWT2025] Georgiev, Bogdan; Gómez-Serrano, Javier; Tao, Terence; Wagner, Adam Zsolt.
  Mathematical exploration and discovery at scale.
  [arXiv:2511.02864](https://arxiv.org/abs/2511.02864)
- [WSZXRYHHMPCHCWDS2025] Wang, Yiping; Su, Shao-Rong; Zeng, Zhiyuan; Xu, Eva; Ren, Liliang; Yang,
  Xinyu; Huang, Zeyi; He, Pengcheng; Cheng, Hao; Chen, Weizhu; Wang, Shuohang; Du, Simon Shaolei;
  Shen, Yelong. ThetaEvolve: Test-time Learning on Open Problems.
  [arXiv:2511.23473](https://arxiv.org/abs/2511.23473)
- [YLTLYSTYLLGDHZSWZSHMELCZX2026] Haotian Ye, Haowei Lin, Jingyi Tang, Yizhen Luo, Caiyin Yang,
  Chang Su, Rahul Thapa, Rui Yang, Ruihua Liu, Zeyu Li, Chong Gao, Dachao Ding, Guangrong He,
  Miaolei Zhang, Lina Sun, Wenyang Wang, Yuchen Zhong, Zhuohao Shen, Di He, Jianzhu Ma, Stefano
  Ermon, Tongyang Li, Xiaowen Chu, James Zou, Yuzhi Xu, Evaluation-driven Scaling for Scientific
  Discovery, https://arxiv.org/abs/2604.19341
- [YKLBMWKCZGS2026] Yuksekgonul, Mert; Koceja, Daniel; Li, Xinhao; Bianchi, Federico; McCaleb, Jed;
  Wang, Xiaolong; Kautz, Jan; Choi, Yejin; Zou, James; Guestrin, Carlos; Sun, Yu. [Learning to
  Discover at Test Time](https://test-time-training.github.io/discover.pdf), 2026.
- [T2026] Together AI. Einsteinarena-new-sota: State-of-the-art results on open math problems, 2026.
  URL https://github.com/togethercomputer/EinsteinArena-new-SOTA.
-/

open Set

namespace Constant1a

/-- **Tao's Optimization constant 1a / An autocorrelation constant related to Sidon sets**:
The biggest real number satisfying a certain inequality about (auto)convolutions
and $L^2$-norms of functions.
This number is related to the maximal size of Sidon sets in additive combinatorics. -/
@[optimization_constant "1a"]
noncomputable def C1a : ℝ :=
  sSup {C : ℝ | ∀ ⦃f : ℝ → ℝ⦄, 0 ≤ f →  C * (∫ x in (- 1 / 4)..(1 / 4), f x) ^ 2
    ≤ sSup {∫ x, f (t - x) * f x | t ∈ Icc (1 / 2 : ℝ) 1}}

/-- Trivial lower bound. -/
@[category research solved, AMS 5 11 26]
theorem c1a_lower_bound_trivial : 1 ≤ C1a := by
  sorry

/-- Lower bound from [MO2004] (2007). -/
@[category research solved, AMS 5 11 26]
theorem c1a_lower_bound_mo2004 : 1.182778 ≤ C1a := by
  sorry

/-- Lower bound from [MO2009] (2009). -/
@[category research solved, AMS 5 11 26]
theorem c1a_lower_bound_mo2009 : 1.262 ≤ C1a := by
  sorry

/-- Lower bound from [MV2009] (2010). -/
@[category research solved, AMS 5 11 26]
theorem c1a_lower_bound_mv2009 : 1.2748 ≤ C1a := by
  sorry

/-- Lower bound from [CS2017] (2017). -/
@[category research solved, AMS 5 11 26]
theorem c1a_lower_bound_cs2017 : 1.28 ≤ C1a := by
  sorry

/-- Lower bound from [IX2026] (2026). -/
@[category research solved, AMS 5 11 26]
theorem c1a_lower_bound_ix2026 : 1.2802 ≤ C1a := by
  sorry

/-- Lower bound from [PBV2026] (2026). -/
@[category research solved, AMS 5 11 26]
theorem c1a_lower_bound_pbv2026 : 1.292 ≤ C1a := by
  sorry

/-- Upper bound from [SS2002] (2002). -/
@[category research solved, AMS 5 11 26]
theorem c1a_upper_bound_ss2002 : C1a ≤ Real.pi / 2 := by
  sorry

/-- Upper bound from [MV2009] (2010). -/
@[category research solved, AMS 5 11 26]
theorem c1a_upper_bound_mv2009 : C1a ≤ 1.50992 := by
  sorry

/-- Upper bound from [GGSWT2025] (2025). May 2025 announcement, AlphaEvolve -/
@[category research solved, AMS 5 11 26]
theorem c1a_upper_bound_ggswt2025_1 : C1a ≤ 1.5053 := by
  sorry

/-- Upper bound from [GGSWT2025] (2025). Dec 2025 preprint release, AlphaEvolve -/
@[category research solved, AMS 5 11 26]
theorem c1a_upper_bound_ggswt2025_2 : C1a ≤ 1.503164 := by
  sorry

/-- Upper bound from [WSZXRYHHMPCHCWDS2025] (2025). ThetaEvolve -/
@[category research solved, AMS 5 11 26]
theorem c1a_upper_bound_wszxryhhmpchcwds2025 : C1a ≤ 1.503133 := by
  sorry

/-- Upper bound from [YLTLYSTYLLGDHZSWZSHMELCZX2026] (2026). SimpleTES -/
@[category research solved, AMS 5 11 26]
theorem c1a_upper_bound_yltlystyllgdhzswzshmelczx2026 : C1a ≤ 1.503871 := by
  sorry

/-- Upper bound from [YKLBMWKCZGS2026] (2026). TTT-Discover -/
@[category research solved, AMS 5 11 26]
theorem c1a_upper_bound_yklbmwkczgs2026 : C1a ≤ 1.502870 := by
  sorry

/-- Upper bound from [T2026] (2026). TogetherAI -/
@[category research solved, AMS 5 11 26]
theorem c1a_upper_bound_t2026 : C1a ≤ 1.502862 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 11 26]
theorem c1a_eq : answer(sorry) = C1a := by
  sorry

-- TODO: Formalise relationship to Sidon sets.
-- TODO: State results from https://arxiv.org/abs/2602.07292

end Constant1a
