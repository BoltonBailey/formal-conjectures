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
# The Exponential Time Hypothesis

The exponential time hypothesis (ETH) of Impagliazzo and Paturi asserts that $3$-SAT cannot
be solved in time $2^{\delta n}$ for arbitrarily small $\delta > 0$, where $n$ is the number
of variables of the input formula. It is a strengthening of $P \neq NP$ and the basic
assumption underlying much of fine-grained complexity.

Two inequivalent statements circulate under this name, and this file records both.

* The original, **infimum** form: writing $s_k$ for the infimum of those $\delta$ for which
  $k$-SAT admits an $O(2^{\delta n})$ algorithm, ETH states that $s_3 > 0$.
* The **weaker** form: there is no *single* algorithm solving $3$-SAT in time $2^{o(n)}$.

The former implies the latter. The converse is open: it is consistent with current knowledge
that there is a sequence of algorithms with running times $O(2^{\delta_i n})$ for
$\delta_i \to 0$ whose descriptions grow so fast that no single algorithm can select and run
the appropriate one. Collapsing the two would require a "master" algorithm dovetailing an
enumeration of candidates, which is obstructed by the undecidability of recognising which
programs correctly decide $3$-SAT; this is closely related to the open problem of whether
SAT admits an optimal algorithm.

## Machine model

Both forms are stated for the model underlying `ComplexityTheory.IsTimeBounded`, namely
Mathlib's `Turing.FinTM2`: a *deterministic multi-stack machine* with finitely many stacks,
states and function labels. A step is one transition of `Turing.TM2.step`, and the input is
the formula under the `BitstringEncoding` instance on `KCNF k`. Running time is measured
against the number of variables `n`, with the customary factor polynomial in `n + m`, where
`m` is the number of clauses.

None of these choices affect the truth of the statements. Any two reasonable deterministic
models simulate each other with polynomial overhead, and a fixed polynomial overhead only
rescales the exponent: `(2 ^ (δ * n)) ^ c = 2 ^ (c * δ * n)`, and `2 ^ o(n)` raised to a
fixed power is again `2 ^ o(n)`. Since both forms quantify existentially over the exponent,
both transfer. The same argument covers the encoding, which is fixed only up to
polynomial-time transcoding. This robustness is what makes the hypothesis well posed
independently of the model, and it would fail for the *strong* exponential time hypothesis,
which pins down an exact exponent and is by convention a statement about word RAMs.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Exponential_time_hypothesis)
- Russell Impagliazzo and Ramamohan Paturi. On the Complexity of k-SAT.
  Journal of Computer and System Sciences 62(2):367-375, 2001.
- Jörg Flum and Martin Grohe. Parameterized Complexity Theory, Chapter 16.
  Springer, 2006.
-/

namespace ExponentialTimeHypothesis

open ComplexityTheory Asymptotics Filter

/--
`SolvesKSATInTime k T` asserts that some deterministic multi-stack machine
(`Turing.FinTM2`, the model used by `ComplexityTheory.IsTimeBounded`) decides satisfiability
of `k`-CNF formulas, halting on input `f` within `T f` steps of `Turing.TM2.step`.

The input is the formula encoded via the `BitstringEncoding` instance on `KCNF k`; note that
the bound `T f` may depend on the formula itself, and not merely on the length of that
encoding.
-/
def SolvesKSATInTime (k : ℕ) (T : KCNF k → ℕ) : Prop :=
  IsTimeBounded (fun f : KCNF k => CNF.satisfiable f.val) T

/--
The running-time bound `C * 2 ^ (δ * n) * (n + m) ^ c`, where `n` is the number of variables
and `m` the number of clauses of the instance.

The polynomial factor is the one appearing in Impagliazzo and Paturi's definition; unlike the
`2 ^ o(n)` form below, the bound `2 ^ (δ * n)` does not absorb polynomial factors on its own.
Its presence is also what keeps the definition model-independent: without it the bound would
be sensitive to the polynomial simulation overhead between machine models, and on a weak
model even reading the input could exceed it.
-/
noncomputable def timeBound (k : ℕ) (δ C : ℝ) (c : ℕ) (f : KCNF k) : ℕ :=
  ⌈C * (2 : ℝ) ^ (δ * f.val.numVars) * ((f.val.numVars + f.val.length : ℕ) : ℝ) ^ c⌉₊

/--
The set of exponents `δ ≥ 0` for which `k`-SAT can be solved in time
`2 ^ (δ * n) * poly(n + m)` on a deterministic multi-stack machine.

Because `δ` is quantified existentially in `s` below, this set moves under a change of
machine model only by a rescaling that leaves the positivity of its infimum unchanged.
-/
def satExponents (k : ℕ) : Set ℝ :=
  {δ | 0 ≤ δ ∧ ∃ (C : ℝ) (c : ℕ), 0 < C ∧ SolvesKSATInTime k (timeBound k δ C c)}

/--
`s k` is the infimum of the exponents at which `k`-SAT can be solved, written `s_k` by
Impagliazzo and Paturi.

Since `satExponents k` is a set of nonnegative reals it is bounded below, so this is a
genuine infimum rather than the junk value `sInf` takes on unbounded sets. It is however the
junk value `0` should `satExponents k` be empty, so `0 < s k` additionally asserts that some
exponent is achievable at all; this is harmless, as brute-force search over all `2 ^ n`
assignments witnesses `1 ∈ satExponents k`.
-/
noncomputable def s (k : ℕ) : ℝ := sInf (satExponents k)

/--
**The Exponential Time Hypothesis (ETH)**, in the original Impagliazzo-Paturi form:
the infimum `s₃` of the exponents at which `3`-SAT can be solved is strictly positive.

Equivalently, there is some `δ > 0` such that no deterministic multi-stack machine solves
`3`-SAT in time `2 ^ (δ * n) * poly(n + m)`. See the module docstring for why the choice of
machine model does not affect this.
-/
@[category research open, AMS 68]
theorem exponential_time_hypothesis : 0 < s 3 := by
  sorry

/--
`SolvableInSubexponentialTime k` asserts that a *single* deterministic multi-stack machine
decides `k`-SAT in time `2 ^ (g n) * poly(n + m)` for some `g = o(n)`.

The emphasis on a single machine is what distinguishes this from `satExponents` being all of
`Set.Ioi 0`, where a different machine is permitted for each `δ`. Model changes preserve the
distinction, since a simulation is one fixed machine with one fixed polynomial overhead and
so maps a single algorithm to a single algorithm.
-/
def SolvableInSubexponentialTime (k : ℕ) : Prop :=
  ∃ (g : ℕ → ℝ) (C : ℝ) (c : ℕ), (g =o[atTop] fun n : ℕ => (n : ℝ)) ∧ 0 < C ∧
    SolvesKSATInTime k fun f =>
      ⌈C * (2 : ℝ) ^ g f.val.numVars * ((f.val.numVars + f.val.length : ℕ) : ℝ) ^ c⌉₊

/--
**The Exponential Time Hypothesis, weak form**: no single deterministic multi-stack machine
solves `3`-SAT in time `2 ^ o(n) * poly(n + m)`.

This is the form stated by some sources. It is implied by `exponential_time_hypothesis`, and
whether it implies it in turn is open.
-/
@[category research open, AMS 68]
theorem exponential_time_hypothesis_weak : ¬ SolvableInSubexponentialTime 3 := by
  sorry

/--
The Impagliazzo-Paturi form of ETH implies the `2 ^ o(n)` form.

Indeed, an algorithm running in time `2 ^ (g n) * poly(n + m)` with `g = o(n)` runs, for
every `δ > 0`, in time `2 ^ (δ * n) * poly(n + m)` after enlarging the constant to absorb the
finitely many `n` with `g n > δ * n`; hence every `δ > 0` lies in `satExponents 3` and
`s 3 = 0`. The converse implication is open.
-/
@[category API, AMS 68]
theorem not_solvableInSubexponentialTime_of_s_pos (h : 0 < s 3) :
    ¬ SolvableInSubexponentialTime 3 := by
  sorry

end ExponentialTimeHypothesis
