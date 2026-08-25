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
import FormalConjectures.Wikipedia.MoserWorm

/-!
# Tao's Optimization constant 13a / Moser's convex worm cover constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 13a](https://teorth.github.io/optimizationproblems/constants/13a.html)
- [Wan2006] Wang, Wei. "An improved upper bound for the worm problem." Acta Mathematica Sinica
  49 (2006), no. 4, 835–846.
- [KPS2013] Khandhawit, Tirasan; Pagonakis, Dimitrios; Sriswasdi, Sira. "Lower bound for convex
  hull area and universal cover problems." International Journal of Computational Geometry &
  Applications 23 (2013), no. 3, 197–212. [arXiv:1101.5638](https://arxiv.org/abs/1101.5638)
- [PW2021] Panraksa, Chatchawan; Wichiramala, Wacharin. "Wetzel's sector covers unit arcs."
  Periodica Mathematica Hungarica 82 (2021), 213–222.
- [Wet1973] Wetzel, John E. "Sectorial covers for curves of constant length." Canadian Mathematical
  Bulletin 16 (1973), 367–376.
- [KS2009] Khandhawit, Tirasan; Sriswasdi, Sira. "An Improved Lower Bound for Moser's Worm Problem".
  [arXiv:math/0701391](https://arxiv.org/abs/math/0701391) (v2, 2009).
- [G1972] Gerriets, J. "An improved solution to Moser’s worm problem." Unpublished, 1972.
- [GP1974] Gerriets, J.; Poole, G. "An improved solution to Moser’s worm problem." American
  Mathematical Monthly 81 (1974), no. 1, 36–41. DOI: 10.2307/2318213.
- [NPL1992] Norwood, Rick; Poole, George; Laidacker, Michael. "The worm problem of Leo Moser".
  "Discrete & Computational Geometry" 7 (1992), 153–162. DOI: 10.1007/BF02187832.

Worms and worm covers are formalised in `FormalConjectures.Wikipedia.MoserWorm`.
-/

open MeasureTheory
open scoped ENNReal

namespace Constant13a

/-- **Tao's Optimization constant 13a / Moser's convex worm cover constant**:
the infimal area of a convex planar domain that contains a rigid motion of every planar arc of
length $1$. -/
@[optimization_constant "13a"]
noncomputable def C13a : ℝ≥0∞ :=
  sInf {v | ∃ X ∈ MoserWorm.WormCovers, Convex ℝ X ∧ volume X = v}

/-- Lower bound from [Wet1973] (1973). Uses “broadworms” (building on work of Schaer on the broadest
curve of unit length) -/
@[category research solved, AMS 52]
theorem c13a_lower_bound_wet1973 : 0.2194 ≤ C13a := by
  sorry

/-- Lower bound from [KS2009] (2009). Uses “V”-worms (equilateral-triangle hull) and “U”-worms
(square hull) -/
@[category research solved, AMS 52]
theorem c13a_lower_bound_ks2009 : 0.227498 ≤ C13a := by
  sorry

/-- Lower bound from [KPS2013] (2013). Min–max estimate for convex hull area of certain forced
configurations -/
@[category research solved, AMS 52]
theorem c13a_lower_bound_kps2013 : 0.232239 ≤ C13a := by
  sorry

/-- Trivial upper bound. disk of radius $1/2$ -/
@[category research solved, AMS 52]
theorem c13a_upper_bound_trivial : C13a ≤ ENNReal.ofReal (Real.pi / 4) := by
  refine sInf_le ⟨Metric.closedBall 0 0.5, MoserWorm.disc_mem_worm_covers,
    convex_closedBall _ _, ?_⟩
  rw [EuclideanSpace.volume_closedBall]
  rw [Fintype.card_fin]
  norm_num [Real.Gamma_two, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
    Real.sq_sqrt Real.pi_nonneg]
  ring_nf

/-- Upper bound from Meir [Wet1973] (1973). semicircle of radius $1/2$ -/
@[category research solved, AMS 52]
theorem c13a_upper_bound_wet1973_1 : C13a ≤ ENNReal.ofReal (Real.pi / 8) := by
  sorry

/-- Upper bound from [Wet1973] (1973). -/
@[category research solved, AMS 52]
theorem c13a_upper_bound_wet1973_2 : C13a ≤ 0.34501 := by
  sorry

/-- Upper bound from [G1972] (1972). -/
@[category research solved, AMS 52]
theorem c13a_upper_bound_g1972 : C13a ≤ 0.3214 := by
  sorry

/-- Upper bound from [GP1974] (1974). -/
@[category research solved, AMS 52]
theorem c13a_upper_bound_gp1974 : C13a ≤ 0.28610 := by
  sorry

/-- Upper bound from [NPL1992] (1992). -/
@[category research solved, AMS 52]
theorem c13a_upper_bound_npl1992 : C13a ≤ 0.27524 := by
  sorry

/-- Upper bound from [Wan2006] (2006). -/
@[category research solved, AMS 52]
theorem c13a_upper_bound_wan2006 : C13a ≤ 0.270911861 := by
  sorry

/-- Upper bound from [PW2021] (1907). 30° circular sector of radius 1 (“Wetzel’s sector”). Builds
upon [MW2017] -/
@[category research solved, AMS 52]
theorem c13a_upper_bound_pw2021 : C13a ≤ ENNReal.ofReal (Real.pi / 12) := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 52]
theorem c13a_eq : answer(sorry) = C13a := by
  sorry

end Constant13a
