-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.
import Lax759944Proofs.Legacy.Ram
import Mathlib.Data.Set.Basic

/-!
A word RAM program computes a function of words within a time bound *T*
on a set *D* of admissible inputs if, started on any input *x* in *D* at
word length *w*, it halts after at most *T(x)* steps having written the
value of the function at *x* to its output tape. The bound is a function
of the input, so that bounds like "linear in the length of the input"
are stated by instantiating *T*.

# Formalization notes

The number of steps is the machine's own step count, so a time bound is
a statement about the *program*: nothing is annotated onto the program
and then trusted. Only inputs in `D` are constrained; a program is free
to do anything at all on malformed input, which is what a statement
about an algorithm on encoded objects should say.

The bound is stated elementarily — an explicit `T` that the step count
does not exceed — rather than through asymptotic notation. Asymptotics
would require a filter on inputs and would obscure, rather than clarify,
a statement that quantifies over encodings of every graph; a linear
bound is spelled out at the point of use as `c * (x.length + 1)` with an
explicit constant, a fixed-parameter bound as
`c * 2 ^ k * (x.length + 1)` with the parameter dependence written in,
the `+ 1` making both meaningful for the empty input as well.

The word length `w` is an explicit argument, and statements built on
this notion quantify it visibly, in the order
`∃ p, ∀ …, ∀ w, (word-length hypothesis) → ComputesInTime w p D f T`.
The program is quantified *before* the word length: one program that
works at every sufficiently large word length, so that `w` cannot
smuggle advice into the machine — a program chosen after `w` could hide
an arbitrary amount of information in its literals. This is the same
uniformity discipline the quantifier order enforces for the parameter of
a fixed-parameter bound.

Word-length hypotheses are written as explicit inequalities against
`2 ^ w` — `c * (x.length + 1) ≤ 2 ^ w`, or "every entry of `x` is less
than `2 ^ w`" — never through logarithms. This keeps the no-asymptotics
style of the surrounding statements and says exactly what a proof needs:
that the quantities the program manipulates fit into a word. Where
honesty requires it, the same fitting conditions appear in the
admissible set `D` itself, alongside the well-formedness conditions of
the encoding, since the machine reduces oversized input entries modulo
`2 ^ w` rather than rejecting them.

Only the timed notion is defined: every statement built on this machine
carries a bound, and plain computability is the special case in which
`T` is unconstrained.
-/

namespace Lax759944Proofs.Legacy.RamComputes

open Lax759944Proofs.Legacy.Ram

/-- At word length `w`, on every admissible input `x`, the program halts
within `T x` steps with output `f x`. -/
def ComputesInTime (w : ℕ) (p : Program) (D : Set (List ℕ))
    (f : List ℕ → List ℕ) (T : List ℕ → ℕ) : Prop :=
  ∀ x ∈ D, ∃ t ≤ T x, RunsTo w p x (f x) t

end Lax759944Proofs.Legacy.RamComputes
