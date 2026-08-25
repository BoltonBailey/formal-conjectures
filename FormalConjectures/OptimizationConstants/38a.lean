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
# Tao's Optimization constant 38a / The square-lattice self-avoiding walk connective constant

⚠️ This file was written by AI and has not been reviewed, it may contain mistakes or
hallucinations.

*References:*
- [Tao's optimization constant 38a](https://teorth.github.io/optimizationproblems/constants/38a.html)
- [CG1993] Conway, A. R.; Guttmann, A. J. "Lower bound on the number of self-avoiding walks."
  Journal of Physics A 26 (1993), 1535–1542.
- [Jen2004] Jensen, I. "Improved lower bounds on the connective constants for two-dimensional
  self-avoiding walks." Journal of Physics A 37 (2004), 5503–5524.
- [PT2000] Pönitz, A.; Tittmann, P. "Improved upper bounds for self-avoiding walks in
  $\mathbb{Z}^d$." Electronic Journal of Combinatorics 7 (2000), R21.
- [FV2017] Friedli, S.; Velenik, Y. "Statistical Mechanics of Lattice Systems." Cambridge
  University Press (2017).
- [SlaBounds] Slade, Gordon. "Bounds on the self-avoiding-walk connective constant." In: Benedetto,
  John J. (ed.), "The Journal of Fourier Analysis and Applications." CRC Press (2020), 525–533. DOI:
  [10.1201/9780429332838-32](https://doi.org/10.1201/9780429332838-32). [Author
  PDF](https://personal.math.ubc.ca/~slade/kahane.pdf).
- [Num2026] Numaro ([numaro.tech](https://numaro.tech)). "An improved rigorous lower bound for the
  square-lattice SAW connective constant." [Certificate
  archive](https://doi.org/10.5281/zenodo.21546041), submitted to this repository (2026).
-/

open Filter

namespace Constant38a

/-- A **self-avoiding walk** of length $n$ in the square lattice, encoded as an injective path
$p : \{0, \ldots, n\} \to \mathbb{Z}^2$ starting at the origin whose consecutive points are
nearest neighbours. -/
def IsSAW (n : ℕ) (p : Fin (n + 1) → ℤ × ℤ) : Prop :=
  p 0 = 0 ∧ Function.Injective p ∧
    ∀ i : Fin n, |(p i.succ).1 - (p i.castSucc).1| + |(p i.succ).2 - (p i.castSucc).2| = 1

/-- The number $c_n$ of self-avoiding walks of length $n$ starting at the origin. -/
noncomputable def sawCount (n : ℕ) : ℕ := Nat.card {p : Fin (n + 1) → ℤ × ℤ // IsSAW n p}

/-- **Tao's Optimization constant 38a / The square-lattice self-avoiding walk connective
constant**: $\mu_{\mathbb{Z}^2} = \lim_n c_n^{1/n}$. We take a `limsup`; for the square lattice
the limit is known to exist by submultiplicativity. -/
@[optimization_constant "38a"]
noncomputable def C38a : ℝ := limsup (fun n : ℕ => (sawCount n : ℝ) ^ ((n : ℝ)⁻¹)) atTop

/-- Trivial lower bound. From the general bound $d \le \mu \le 2d-1$ with $d=2$. [SlaBounds-simple]
-/
@[category research solved, AMS 5 82]
theorem c38a_lower_bound_trivial : 2 ≤ C38a := by
  classical
  have hbox : ∀ (n : ℕ) (p : Fin (n + 1) → ℤ × ℤ), IsSAW n p →
      ∀ k : ℕ, ∀ hk : k < n + 1,
        (p ⟨k, hk⟩).1.natAbs + (p ⟨k, hk⟩).2.natAbs ≤ k := by
    intro n p hp
    obtain ⟨h0, -, hstep⟩ := hp
    intro k
    induction k with
    | zero =>
      intro hk
      have hz : (⟨0, hk⟩ : Fin (n + 1)) = 0 := rfl
      rw [hz, h0]
      simp
    | succ j ih =>
      intro hk
      have hj : j < n := by omega
      have hj1 : j < n + 1 := by omega
      have hs := hstep ⟨j, hj⟩
      have hsucc : (⟨j, hj⟩ : Fin n).succ = (⟨j + 1, hk⟩ : Fin (n + 1)) := rfl
      have hcast : (⟨j, hj⟩ : Fin n).castSucc = (⟨j, hj1⟩ : Fin (n + 1)) := rfl
      rw [hsucc, hcast] at hs
      have habs : ((p ⟨j + 1, hk⟩).1 - (p ⟨j, hj1⟩).1).natAbs
          + ((p ⟨j + 1, hk⟩).2 - (p ⟨j, hj1⟩).2).natAbs = 1 := by
        rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hs
        exact_mod_cast hs
      have e1 : (p ⟨j + 1, hk⟩).1
          = (p ⟨j, hj1⟩).1 + ((p ⟨j + 1, hk⟩).1 - (p ⟨j, hj1⟩).1) := by ring
      have e2 : (p ⟨j + 1, hk⟩).2
          = (p ⟨j, hj1⟩).2 + ((p ⟨j + 1, hk⟩).2 - (p ⟨j, hj1⟩).2) := by ring
      have b1 := Int.natAbs_add_le (p ⟨j, hj1⟩).1 ((p ⟨j + 1, hk⟩).1 - (p ⟨j, hj1⟩).1)
      have b2 := Int.natAbs_add_le (p ⟨j, hj1⟩).2 ((p ⟨j + 1, hk⟩).2 - (p ⟨j, hj1⟩).2)
      rw [← e1] at b1
      rw [← e2] at b2
      have hih := ih hj1
      omega
  have hfin : ∀ n : ℕ, {p : Fin (n + 1) → ℤ × ℤ | IsSAW n p}.Finite := by
    intro n
    have hsub : {p : Fin (n + 1) → ℤ × ℤ | IsSAW n p} ⊆
        Set.pi Set.univ
          (fun _ : Fin (n + 1) => (Set.Icc (-(n : ℤ)) n) ×ˢ (Set.Icc (-(n : ℤ)) n)) := by
      intro p hp
      rw [Set.mem_univ_pi]
      intro i
      have hb := hbox n p hp i.val i.isLt
      have hi : (⟨i.val, i.isLt⟩ : Fin (n + 1)) = i := rfl
      rw [hi] at hb
      have hin : i.val ≤ n := by omega
      simp only [Set.mem_prod, Set.mem_Icc]
      omega
    refine Set.Finite.subset ?_ hsub
    exact Set.Finite.pi fun i => (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  have hcount : ∀ n : ℕ, 2 ^ n ≤ sawCount n := by
    intro n
    set S : (Fin n → Bool) → ℕ → Bool :=
      fun s j => if h : j < n then s ⟨j, h⟩ else false with hS
    set A : (Fin n → Bool) → ℕ → ℕ :=
      fun s k => ∑ j ∈ Finset.range k, (if S s j = true then 1 else 0) with hA
    have hA0 : ∀ s, A s 0 = 0 := by intro s; simp [hA]
    have hAsucc : ∀ s k, A s (k + 1) = A s k + (if S s k = true then 1 else 0) := by
      intro s k
      simp only [hA]
      exact Finset.sum_range_succ _ _
    set φ : (Fin n → Bool) → Fin (n + 1) → ℤ × ℤ :=
      fun s k => ((A s k.val : ℤ), (k.val : ℤ) - (A s k.val : ℤ)) with hφ
    have hsaw : ∀ s, IsSAW n (φ s) := by
      intro s
      refine ⟨?_, ?_, ?_⟩
      · simp [hφ, hA0]
      · intro k l hkl
        have h1 : ((k : ℕ) : ℤ) = ((l : ℕ) : ℤ) := by
          have hp1 : (φ s k).1 = (φ s l).1 := by rw [hkl]
          have hp2 : (φ s k).2 = (φ s l).2 := by rw [hkl]
          simp only [hφ] at hp1 hp2
          omega
        exact Fin.ext (by exact_mod_cast h1)
      · intro i
        have hvs : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := Fin.val_succ i
        have hvc : ((i.castSucc : Fin (n + 1)) : ℕ) = (i : ℕ) := Fin.val_castSucc i
        simp only [hφ, hvs, hvc]
        have hb := hAsucc s (i : ℕ)
        by_cases h : S s (i : ℕ) = true
        · rw [if_pos h] at hb
          rw [hb]
          push_cast
          rw [show (A s (i : ℕ) : ℤ) + 1 - (A s (i : ℕ) : ℤ) = 1 by ring]
          rw [show ((i : ℕ) : ℤ) + 1 - ((A s (i : ℕ) : ℤ) + 1) - (((i : ℕ) : ℤ)
            - (A s (i : ℕ) : ℤ)) = 0 by ring]
          simp
        · rw [if_neg h] at hb
          rw [hb]
          push_cast
          rw [show (A s (i : ℕ) : ℤ) + 0 - (A s (i : ℕ) : ℤ) = 0 by ring]
          rw [show ((i : ℕ) : ℤ) + 1 - ((A s (i : ℕ) : ℤ) + 0) - (((i : ℕ) : ℤ)
            - (A s (i : ℕ) : ℤ)) = 1 by ring]
          simp
    have hinj : Function.Injective fun s : Fin n → Bool => (⟨φ s, hsaw s⟩ :
        {p : Fin (n + 1) → ℤ × ℤ // IsSAW n p}) := by
      intro s t hst
      have hst' : φ s = φ t := congrArg Subtype.val hst
      funext i
      have h1 : (φ s i.castSucc).1 = (φ t i.castSucc).1 := by rw [hst']
      have h2 : (φ s i.succ).1 = (φ t i.succ).1 := by rw [hst']
      simp only [hφ, Fin.val_succ, Fin.val_castSucc] at h1 h2
      have e1 := hAsucc s (i : ℕ)
      have e2 := hAsucc t (i : ℕ)
      have hSst : S s (i : ℕ) = S t (i : ℕ) := by
        by_cases hs : S s (i : ℕ) = true <;> by_cases ht : S t (i : ℕ) = true <;>
          simp_all
      simpa [hS, i.isLt] using hSst
    have hfinite : Finite {p : Fin (n + 1) → ℤ × ℤ // IsSAW n p} := (hfin n).to_subtype
    have hcard := Nat.card_le_card_of_injective _ hinj
    simpa [sawCount] using hcard
  have hub : ∀ n : ℕ, sawCount n ≤ 4 ^ n := by
    intro n
    set T : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)} with hT
    have hmemT : ∀ x y : ℤ × ℤ, |x.1 - y.1| + |x.2 - y.2| = 1 → x - y ∈ T := by
      intro x y hxy
      have hnat : (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1 := by
        rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hxy
        exact_mod_cast hxy
      have hxy' : x - y = (x.1 - y.1, x.2 - y.2) := rfl
      rw [hxy', hT]
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      omega
    have hstepdet : ∀ (p q : Fin (n + 1) → ℤ × ℤ), IsSAW n p → IsSAW n q →
        (∀ i : Fin n, p i.succ - p i.castSucc = q i.succ - q i.castSucc) →
        ∀ k : ℕ, ∀ hk : k < n + 1, p ⟨k, hk⟩ = q ⟨k, hk⟩ := by
      intro p q hp hq hstep k
      induction k with
      | zero =>
        intro hk
        have h0 : (⟨0, hk⟩ : Fin (n + 1)) = 0 := rfl
        rw [h0, hp.1, hq.1]
      | succ j ih =>
        intro hk
        have hj : j < n := by omega
        have hj1 : j < n + 1 := by omega
        have hs := hstep ⟨j, hj⟩
        have hsucc : (⟨j, hj⟩ : Fin n).succ = (⟨j + 1, hk⟩ : Fin (n + 1)) := rfl
        have hcast : (⟨j, hj⟩ : Fin n).castSucc = (⟨j, hj1⟩ : Fin (n + 1)) := rfl
        rw [hsucc, hcast, ih hj1] at hs
        exact sub_left_inj.mp hs
    have hfinite : Finite {p : Fin (n + 1) → ℤ × ℤ // IsSAW n p} := (hfin n).to_subtype
    have hinj : Function.Injective
        (fun P : {p : Fin (n + 1) → ℤ × ℤ // IsSAW n p} =>
          fun i : Fin n => (⟨P.1 i.succ - P.1 i.castSucc, hmemT _ _ (P.2.2.2 i)⟩ : ↥T)) := by
      intro P Q hPQ
      have hsteps : ∀ i : Fin n, P.1 i.succ - P.1 i.castSucc = Q.1 i.succ - Q.1 i.castSucc := by
        intro i
        exact congrArg Subtype.val (congrFun hPQ i)
      refine Subtype.ext ?_
      funext k
      have hk := hstepdet P.1 Q.1 P.2 Q.2 hsteps k.val k.isLt
      simpa using hk
    have hcard := Nat.card_le_card_of_injective _ hinj
    have hTcard : T.card = 4 := by decide
    have hcodom : Nat.card (Fin n → ↥T) = 4 ^ n := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe, hTcard,
        Fintype.card_fin]
    rw [hcodom] at hcard
    simpa [sawCount] using hcard
  refine le_limsup_of_frequently_le ((eventually_gt_atTop 0).frequently.mono fun n hn => ?_)
    (Filter.isBoundedUnder_of ⟨4, fun n => ?_⟩)
  · have h2 : ((2 : ℝ) ^ (n : ℕ)) ≤ (sawCount n : ℝ) := by exact_mod_cast hcount n
    calc (2 : ℝ) = ((2 : ℝ) ^ (n : ℕ)) ^ ((n : ℝ)⁻¹) := by
          rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num),
            mul_inv_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
      _ ≤ (sawCount n : ℝ) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h2 (by positivity)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have h4 : ((sawCount n : ℝ)) ≤ (4 : ℝ) ^ (n : ℕ) := by exact_mod_cast hub n
      calc (sawCount n : ℝ) ^ ((n : ℝ)⁻¹)
          ≤ ((4 : ℝ) ^ (n : ℕ)) ^ ((n : ℝ)⁻¹) :=
            Real.rpow_le_rpow (by positivity) h4 (by positivity)
        _ = 4 := by
            rw [← Real.rpow_natCast (4 : ℝ) n, ← Real.rpow_mul (by norm_num),
              mul_inv_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]

/-- Lower bound from [SlaBounds] (2020). Reported (Table 1) as the best rigorous lower bound for
$d=2$ in this survey; the survey attributes it to [CG1993]. [SlaBounds-table1-d2]
[SlaBounds-conway-guttmann] -/
@[category research solved, AMS 5 82]
theorem c38a_lower_bound_slabounds : 2.62002 ≤ C38a := by
  sorry

/-- Lower bound from [FV2017] (2017). Reported as a rigorous lower bound in [FV2017] (attributed
there to [Jen2004-lb]). [FV2017-bounds-square] [FV2017-ref-182] -/
@[category research solved, AMS 5 82]
theorem c38a_lower_bound_fv2017 : 2.625622 ≤ C38a := by
  sorry

/-- Lower bound from [Num2026] (2026). Kesten irreducible-bridge renewal exactly as in [Jen2004-lb],
extended two span levels past the 2004 computation (span $L=17$, series length $N=260$) by an exact
cell-by-cell finite-lattice transfer matrix (CRT big-integer arithmetic); the certificate is a
single exact big-integer inequality (self-contained checker included), and secondary certificates at
Jensen's own span ($L=15$, $N=260$ gives $2.6256270$) and at $L=16$ ($2.6265705$) independently also
exceed $2.625622$. [Num2026-bound] -/
@[category research solved, AMS 5 82]
theorem c38a_lower_bound_num2026 : 2.6273856 ≤ C38a := by
  sorry

/-- Trivial upper bound. From the general bound $d \le \mu \le 2d-1$ with $d=2$. [SlaBounds-simple]
-/
@[category research solved, AMS 5 82]
theorem c38a_upper_bound_trivial : C38a ≤ 3 := by
  sorry

/-- Upper bound from [SlaBounds] (2020). Reported (Table 1) as the best rigorous upper bound for
$d=2$ in this survey, attributed there to [Alm1993]. [SlaBounds-table1-d2] -/
@[category research solved, AMS 5 82]
theorem c38a_upper_bound_slabounds : C38a ≤ 2.69576 := by
  sorry

/-- Upper bound from [FV2017] (2017). Reported as a rigorous upper bound in [FV2017] (attributed
there to [PT2000]). [FV2017-bounds-square] [FV2017-ref-277] -/
@[category research solved, AMS 5 82]
theorem c38a_upper_bound_fv2017 : C38a ≤ 2.679193 := by
  sorry

/-- What is the exact value of the constant? -/
@[category research open, AMS 5 82]
theorem c38a_eq : answer(sorry) = C38a := by
  sorry

end Constant38a
