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

public import FormalConjecturesForMathlib.Computability.BitstringEncoding

/-!
# Conjunctive normal form and the satisfiability problem

This file defines formulas in conjunctive normal form, their satisfiability, and the
width restriction cutting out `k`-CNF formulas. These are the ingredients needed to state
the `k`-SAT problem, and hence the exponential time hypothesis.

Formulas are represented in an untyped, "DIMACS-like" way: variables are natural numbers,
a literal is a variable together with a sign, and a formula is a list of lists of literals.
Keeping the representation non-dependent means the `BitstringEncoding` instances for `ℕ`,
`Bool`, products and lists assemble into an encoding of formulas automatically.

*References:*
- Sanjeev Arora and Boaz Barak. Computational Complexity: A Modern Approach.
  Cambridge University Press, 2009.
-/

@[expose] public section

namespace ComplexityTheory

/--
A literal is a variable index together with a sign: `(i, true)` is the literal `xᵢ` and
`(i, false)` is the literal `¬xᵢ`.
-/
abbrev Literal := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Literal

/-- A formula in conjunctive normal form is a conjunction of clauses. -/
abbrev CNF := List Clause

namespace CNF

/-- The value of a literal under an assignment of truth values to the variables. -/
def evalLiteral (a : ℕ → Bool) (l : Literal) : Bool := a l.1 == l.2

/-- A clause is true under an assignment when at least one of its literals is. -/
def evalClause (a : ℕ → Bool) (c : Clause) : Bool := c.any (evalLiteral a)

/-- A formula is true under an assignment when all of its clauses are. -/
def eval (f : CNF) (a : ℕ → Bool) : Bool := f.all (evalClause a)

/-- A formula is satisfiable when some assignment makes it true. -/
def Satisfiable (f : CNF) : Prop := ∃ a : ℕ → Bool, f.eval a = true

/--
The satisfiability problem, as a `Bool`-valued function.

This is `noncomputable` only in that we supply no decision procedure for it; that is
immaterial to the statements below, which concern the existence of Turing machines
computing this function.
-/
noncomputable def satisfiable (f : CNF) : Bool := @decide f.Satisfiable (Classical.dec _)

@[simp]
theorem satisfiable_eq_true {f : CNF} : f.satisfiable = true ↔ f.Satisfiable := by
  simp [satisfiable]

/-- The (finite) set of variables occurring in a formula. -/
def vars (f : CNF) : Finset ℕ := (f.flatten.map Prod.fst).toFinset

/-- The number of distinct variables occurring in a formula, written `n` in the literature. -/
def numVars (f : CNF) : ℕ := f.vars.card

/-- A formula is a `k`-CNF formula when each of its clauses has at most `k` literals. -/
def IsKCNF (k : ℕ) (f : CNF) : Prop := ∀ c ∈ f, c.length ≤ k

instance (k : ℕ) (f : CNF) : Decidable (IsKCNF k f) :=
  inferInstanceAs (Decidable (∀ c ∈ f, c.length ≤ k))

/- ## Sanity checks -/

/-- The empty conjunction is satisfiable. -/
@[simp]
theorem satisfiable_nil : Satisfiable [] := ⟨fun _ => false, rfl⟩

/-- A formula containing the empty clause is unsatisfiable. -/
theorem not_satisfiable_of_nil_mem {f : CNF} (h : [] ∈ f) : ¬ Satisfiable f := by
  rintro ⟨a, ha⟩
  simpa [evalClause] using (List.all_eq_true.mp ha) [] h

end CNF

/-- The type of `k`-CNF formulas, i.e. those whose clauses have at most `k` literals. -/
abbrev KCNF (k : ℕ) := {f : CNF // CNF.IsKCNF k f}

noncomputable instance (k : ℕ) : BitstringEncoding (KCNF k) := BitstringEncoding.ofSubtype

end ComplexityTheory
