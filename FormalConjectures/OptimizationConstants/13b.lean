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
# Tao's Optimization constant 13b / The Lebesgue universal covering constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 13b](https://teorth.github.io/optimizationproblems/constants/13b.html)
- [Pal1920] Pál, J. "Über ein elementares Variationsproblem." Danske Videnskabernes Selskab
  Mathematisk-fysiske Meddelelser III 2 (1920).
- [Elek1994] Elekes, G. Lower bounds for the universal cover problem, 1994.
- [BS2005] Brass, P.; Sharifi, M. "A lower bound for Lebesgue's universal cover problem."
  International Journal of Computational Geometry & Applications 15 (2005), 537–544.
- [Gib2018] Gibbs, P. "An upper bound for Lebesgue's covering problem."
  [arXiv:1810.10089](https://arxiv.org/abs/1810.10089)
- [Spr1936] Sprague, Roland. *"Über ein elementares Variationsproblem"". "Matematiska Tidsskrift*
  Ser. B (1936), 96–99.
- [Han1992] Hansen, H. C. *"Small universal covers for sets of unit diameter"". "Geometriae
  Dedicata* 42 (1992), 205–213. DOI: 10.1007/BF00147549.
- [BBG2015] Baez, John C.; Bagdasaryan, Karine; Gibbs, Philip. *"The Lebesgue universal covering
  problem"". "Journal of Computational Geometry* 6 (2015), no. 1, 288–299. Preprint:
  https://arxiv.org/abs/1502.01251 (Also available as a PDF from Baez’s webpage:
  https://math.ucr.edu/home/baez/covering.pdf)
-/

open MeasureTheory
open scoped EuclideanGeometry ENNReal

namespace Constant13b

/-- The convex planar sets of diameter $1$. -/
def UnitDiameterConvexSets : Set (Set ℝ²) := {s | Convex ℝ s ∧ Metric.diam s = 1}

/-- The convex universal covers: measurable convex sets that cover a congruent copy of every
convex planar set of diameter $1$. Congruences here include reflections. -/
def UniversalCovers : Set (Set ℝ²) :=
  {X | MeasurableSet X ∧ Convex ℝ X ∧ ∀ s ∈ UnitDiameterConvexSets,
    ∃ (e : ℝ² ≃ₗᵢ[ℝ] ℝ²) (v : ℝ²), s ⊆ (fun x => e x + v) '' X}

/-- **Tao's Optimization constant 13b / The Lebesgue universal covering constant**:
the infimal area of a convex planar set that covers a congruent copy of every convex planar set
of diameter $1$. -/
@[optimization_constant "13b"]
noncomputable def C13b : ℝ≥0∞ := sInf {v | ∃ X ∈ UniversalCovers, volume X = v}

/-- Trivial lower bound. Use unit disk -/
@[category research solved, AMS 52]
theorem c13b_lower_bound_trivial : ENNReal.ofReal (Real.pi / 4) ≤ C13b := by
  refine le_sInf ?_
  rintro v ⟨X, ⟨hXmeas, hXconv, hXcov⟩, rfl⟩
  obtain ⟨e, w, hsub⟩ := hXcov (Metric.closedBall 0 (1 / 2))
    ⟨convex_closedBall _ _, by
      rw [Metric.diam_closedBall_eq _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]; norm_num⟩
  have himg : (fun x => e x + w) '' X = (fun y => y + w) '' (⇑e '' X) := by
    rw [← Set.image_comp]; rfl
  have himgpre : (⇑e '' X) = ⇑e.symm ⁻¹' X := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro h; exact ⟨e.symm y, h, by simp⟩
  have hvol : volume ((fun x : ℝ² => e x + w) '' X) = volume X := by
    rw [himg, Set.image_add_right, measure_preimage_add_right, himgpre,
      (LinearIsometryEquiv.measurePreserving e.symm).measure_preimage hXmeas.nullMeasurableSet]
  have hball : volume (Metric.closedBall (0 : ℝ²) (1 / 2)) = ENNReal.ofReal (Real.pi / 4) := by
    rw [EuclideanSpace.volume_closedBall, Fintype.card_fin]
    norm_num [Real.Gamma_two, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
      Real.sq_sqrt Real.pi_nonneg]
    ring_nf
  calc ENNReal.ofReal (Real.pi / 4) = volume (Metric.closedBall (0 : ℝ²) (1 / 2)) := hball.symm
    _ ≤ volume ((fun x : ℝ² => e x + w) '' X) := measure_mono hsub
    _ = volume X := hvol

/-- Lower bound from [Elek1994] (1994). Use unit disk and equilateral triangle -/
@[category research solved, AMS 52]
theorem c13b_lower_bound_elek1994_1 : 0.8257 ≤ C13b := by
  sorry

/-- Lower bound from [Elek1994] (1994). Also use regular $3^j$-gons -/
@[category research solved, AMS 52]
theorem c13b_lower_bound_elek1994_2 : 0.8271 ≤ C13b := by
  sorry

/-- Lower bound from [BS2005] (2005). Rigorous computer-aided search using a circle, equilateral
triangle, and regular pentagon -/
@[category research solved, AMS 52]
theorem c13b_lower_bound_bs2005 : 0.832 ≤ C13b := by
  sorry

/-- Trivial upper bound. Follows from Jung’s theorem [Elek1994]. -/
@[category research solved, AMS 52]
theorem c13b_upper_bound_trivial : C13b ≤ ENNReal.ofReal (Real.pi / 3) := by
  sorry

/-- Upper bound from [Pal1920] (1920). Regular hexagon circumscribing unit disk. -/
@[category research solved, AMS 52]
theorem c13b_upper_bound_pal1920_1 : C13b ≤ ENNReal.ofReal (Real.sqrt 3 / 2) := by
  sorry

/-- Upper bound from [Pal1920] (1920). Truncation of the hexagon via an inscribed regular dodecagon.
-/
@[category research solved, AMS 52]
theorem c13b_upper_bound_pal1920_2 : C13b ≤ ENNReal.ofReal (2 - 2 / Real.sqrt 3) := by
  sorry

/-- Upper bound from [Spr1936] (1936). Removed a further tiny region -/
@[category research solved, AMS 52]
theorem c13b_upper_bound_spr1936 : C13b ≤ 0.844137708436 := by
  sorry

/-- Upper bound from [Han1992] (corrected in [BBG2015]) (1992, 2015). Removed two additional
microscopic regions -/
@[category research solved, AMS 52]
theorem c13b_upper_bound_han1992_bbg2015 : C13b ≤ 0.844137708398 := by
  sorry

/-- Upper bound from [BBG2015] (2015). Computer-assisted geometry, with high-precision verification
by Greg Egan. -/
@[category research solved, AMS 52]
theorem c13b_upper_bound_bbg2015 : C13b ≤ 0.844115297128419059 := by
  sorry

/-- Upper bound from [Gib2018] (1810). -/
@[category research solved, AMS 52]
theorem c13b_upper_bound_gib2018 : C13b ≤ 0.8440935944 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 52]
theorem c13b_eq : answer(sorry) = C13b := by
  sorry

end Constant13b
