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
import FormalConjectures.ErdosProblems.«16»

/-!
# Tao's Optimization constant 45a / Romanoff's constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 45a](https://teorth.github.io/optimizationproblems/constants/45a.html)
- [R1934] Romanoff, N. P. "Über einige Sätze der additiven Zahlentheorie." Mathematische Annalen
  109 (1934), 668–678.
- [E1950] Erdős, P. "On integers of the form $2^k + p$ and some related problems." Summa Brasil.
  Math. 2 (1950), 113–123.
- [CE2018] Chen, Y.-G.; Elsholtz, C. "Lower bounds for Romanoff's constant." 2018.
- [Y2026] Upper bound $0.490180063290061$, 2026.
- [CS2004] Y.G. Chen and X.G. Sun, "On Romanoff's constant," J. Number Theory, 106 (2004), 275–284.
- [P2006] J. Pintz, "A note on Romanoff's constant," Acta Mathematica Hungarica, 112 (2006), 1-14.
- [HS2010] L. Habsieger and R. Sivak-Fischler, "A new lower bound for Romanoff's constant," Journal
  of Number Theory, 130 (2010).
- [HR2006] L. Habsieger and X. Roblot, "On integers of the form $p + 2^k$," Acta Arithmetica, 122
  (2006), 45–50.
- [CDL2024] Y. Chen, X. Dai, and H. Li, "Some results on a conjecture of de Polignac about numbers
  of the form $p + 2^k$," [arXiv:2402.06644](https://arxiv.org/abs/2402.06644), 2024.
- [G2026] Griego, Sebastian. 36-prime obstruction certificate for Romanoff's constant upper-density
  bound, 2026. [Code and
  verification](https://github.com/sebastian-griego/c45-romanoff-certificate/tree/v1-c45-certificate).

The complementary set is formalised in `FormalConjectures.ErdosProblems.«16»` as
`Erdos16.Erdos16Set`.
-/

open Filter Nat

namespace Constant45a

open scoped Classical in
/-- **Tao's Optimization constant 45a / Romanoff's constant**:
the asymptotic density of the set of odd integers of the form $p + 2^k$ with $p$ prime and
$k \ge 0$. The density is not known to exist, so we take a `limsup`. -/
@[optimization_constant "45a"]
noncomputable def C45a : ℝ :=
  limsup (fun N : ℕ =>
    (count (fun n => Odd n ∧ ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p) N : ℝ) / N) atTop

/-- Trivial lower bound. -/
@[category research solved, AMS 11]
theorem c45a_lower_bound_trivial : 0 ≤ C45a := by
  have hle : ∀ (p : ℕ → Prop) (inst : DecidablePred p) (N : ℕ), @Nat.count p inst N ≤ N :=
    fun p inst N => @Nat.count_le p inst N
  refine le_limsup_of_frequently_le (Frequently.of_forall fun N => by positivity)
    (Filter.isBoundedUnder_of ⟨1, fun N => ?_⟩)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_one (by exact_mod_cast hN)]
    exact Nat.cast_le.mpr (hle _ _ N)

/-- Lower bound from [R1934] (1934). -/
@[category research solved, AMS 11]
theorem c45a_lower_bound_r1934 : 0 < C45a := by
  sorry

/-- Lower bound from [CS2004] (2004). -/
@[category research solved, AMS 11]
theorem c45a_lower_bound_cs2004 : 0.0868 ≤ C45a := by
  sorry

/-- Lower bound from [P2006] (2006). -/
@[category research solved, AMS 11]
theorem c45a_lower_bound_p2006 : 0.0936 ≤ C45a := by
  sorry

/-- Lower bound from [HS2010] (2010). -/
@[category research solved, AMS 11]
theorem c45a_lower_bound_hs2010 : 0.093627 ≤ C45a := by
  sorry

/-- Lower bound from [CE2018] (2018). -/
@[category research solved, AMS 11]
theorem c45a_lower_bound_ce2018 : 0.107648 ≤ C45a := by
  sorry

/-- Trivial upper bound. -/
@[category research solved, AMS 11]
theorem c45a_upper_bound_trivial : C45a ≤ 1 / 2 := by
  have key : ∀ (p : ℕ → Prop) (inst : DecidablePred p), (∀ n, p n → Odd n) →
      ∀ N : ℕ, ((@Nat.count p inst N : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
    intro p inst hp N
    have hnat : ∀ M : ℕ, @Nat.count p inst M ≤ M / 2 := by
      intro M
      induction M with
      | zero => simp
      | succ n ih =>
        rw [Nat.count_succ]
        split_ifs with h
        · have hn : n % 2 = 1 := Nat.odd_iff.mp (hp n h)
          omega
        · omega
    calc ((@Nat.count p inst N : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hnat N
      _ ≤ (N : ℝ) / 2 := Nat.cast_div_le
  refine limsup_le_of_le (Filter.isCoboundedUnder_le_of_le _
    (fun N => by positivity)) (Eventually.of_forall fun N => ?_)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_iff₀ (by exact_mod_cast hN)]
    refine le_trans (key _ _ ?hodd N) ?hfin
    case hodd => rintro n ⟨h, -⟩; exact h
    case hfin => linarith

/-- Upper bound from [E1950] (1950). Used covering systems -/
@[category research solved, AMS 11]
theorem c45a_upper_bound_e1950 : C45a < 0.5 := by
  sorry

/-- Upper bound from [HR2006] (2006). -/
@[category research solved, AMS 11]
theorem c45a_upper_bound_hr2006 : C45a ≤ 0.490941 := by
  sorry

/-- Upper bound from [CDL2024] (2024). -/
@[category research solved, AMS 11]
theorem c45a_upper_bound_cdl2024 : C45a ≤ 0.490341088858244 := by
  sorry

/-- Upper bound from [G2026] (2026). 36-prime finite obstruction certificate with exact
cluster-update verification. -/
@[category research solved, AMS 11]
theorem c45a_upper_bound_g2026 : C45a ≤ 0.490249407811155 := by
  sorry

/-- Upper bound from [Y2026] (2026). -/
@[category research solved, AMS 11]
theorem c45a_upper_bound_y2026 : C45a ≤ 0.490180063290061 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 11]
theorem c45a_eq : answer(sorry) = C45a := by
  sorry

end Constant45a
