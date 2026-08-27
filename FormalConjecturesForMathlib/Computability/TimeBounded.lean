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
module

public import FormalConjecturesForMathlib.Computability.Complexity

/-!
# Instance-dependent time bounds

Mathlib's `Turing.TM2ComputableInTime` bounds the running time of a machine by a function of
the *length of the encoded input*. Several statements in complexity theory instead measure
the running time against a parameter of the instance which is not determined by its size: the
exponential time hypothesis, for example, bounds the time taken on a CNF formula in terms of
its number of *variables*, while the formula itself may have arbitrarily many clauses.

This file provides `IsTimeBounded f T`, asserting that some Turing machine computes `f` and
halts on input `a` within `T a` steps, where the bound `T` is an arbitrary function of the
input rather than of its length.

## Machine model

The model is the same one Mathlib's `Turing.TM2Computable` hierarchy uses, namely
`Turing.FinTM2`: a *deterministic multi-stack machine* with finitely many stacks, finitely
many internal states and function labels, and designated input and output stacks. It is not
a single-tape Turing machine, and "steps" counts transitions of `Turing.TM2.step`, so
constant and polynomial factors in the step count are model-specific.

Statements which quantify existentially over an exponent, such as the exponential time
hypothesis, are insensitive to this choice, since reasonable deterministic models simulate
one another with polynomial overhead and raising a bound `2 ^ (δ * n)` to a fixed power only
rescales `δ`. Statements pinning down an exact exponent or an exact polynomial degree are
not, and should not be phrased against this model without further care.

*References:*
- Sanjeev Arora and Boaz Barak. Computational Complexity: A Modern Approach.
  Cambridge University Press, 2009.
-/

@[expose] public section

open Computability Turing

namespace ComplexityTheory

/--
A deterministic multi-stack machine (`Turing.FinTM2`) together with a proof that it outputs
`f a` on input `a`, using at most `T a` steps of `Turing.TM2.step`.

This differs from `Turing.TM2ComputableInTime` in that the step bound may depend on the input
itself and not merely on its encoded length.
-/
structure TM2ComputableWithin {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (f : α → β) (T : α → ℕ) extends TM2ComputableAux αΓ βΓ where
  /-- proof that this machine outputs `f a` on input `a` within `T a` steps -/
  outputsFun :
    ∀ a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a)))) (T a)

/--
`IsTimeBoundedWithEncoding ea eb f T` asserts that `f` is computed by some deterministic
multi-stack machine (`Turing.FinTM2`) which, on input `a`, halts within `T a` steps of
`Turing.TM2.step`, when its input and output are encoded via the given `Encoding`s `ea` and
`eb`.
-/
def IsTimeBoundedWithEncoding {α β Γα Γβ : Type} (ea : Encoding α Γα) (eb : Encoding β Γβ)
    (f : α → β) (T : α → ℕ) : Prop :=
  Nonempty (TM2ComputableWithin ea.encode eb.encode f T)

/--
`IsTimeBounded f T` asserts that some deterministic multi-stack machine (`Turing.FinTM2`)
computes `f`, halting on input `a` within `T a` steps of `Turing.TM2.step`, for the canonical
`Bool`-alphabet encodings given by the `BitstringEncoding` typeclass.
-/
def IsTimeBounded {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) (T : α → ℕ) : Prop :=
  IsTimeBoundedWithEncoding (BitstringEncoding.toEncoding (α := α))
    (BitstringEncoding.toEncoding (α := β)) f T

/-- A time bound may always be relaxed. -/
theorem IsTimeBounded.mono {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} {T T' : α → ℕ} (h : IsTimeBounded f T) (hT : ∀ a, T a ≤ T' a) :
    IsTimeBounded f T' :=
  h.elim fun M => ⟨M.toTM2ComputableAux, fun a =>
    ⟨(M.outputsFun a).toEvalsTo, (M.outputsFun a).steps_le_m.trans (hT a)⟩⟩

/-- A polynomial-time computable function is time bounded by a polynomial in its input
length, for the same machine model. -/
theorem IsPolyTime.isTimeBounded {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : α → β} (h : IsPolyTime f) :
    ∃ p : Polynomial ℕ,
      IsTimeBounded f fun a => p.eval (BitstringEncoding.bitEncode a).length :=
  h.elim fun M => ⟨M.time, ⟨M.toTM2ComputableAux, M.outputsFun⟩⟩

end ComplexityTheory
