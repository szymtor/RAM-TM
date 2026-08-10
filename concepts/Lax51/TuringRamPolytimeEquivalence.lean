import Lax51.RamPolytime
import Lax51.TuringPolytime

/-!
---
title: Polynomial-time equivalence of Turing machines and word RAMs
type: theorem
---
Finite multi-tape Turing machines and uniform word random access machines
compute exactly the same total functions in polynomial time, when both use
the length of the canonical binary encoding as input size and the word RAM
is required to have a polynomially bounded sufficient word length.

Concretely, a Turing machine must transform the binary encoding of an input
word into the binary encoding of its output in polynomially many Turing
steps. A word RAM receives the same semantic input as a native list of
numbers, physically prefixed by its length so that the input tape is
self-delimiting; one program must return the exact output in polynomially
many RAM instructions at every sufficiently large word length, and a
polynomial in the encoded input length must suffice to represent the length
prefix, all input and output entries, and to make the computation correct.

The claim concerns polynomial-time function computation, commonly called
`FP`. The usual machine-independence statement for the decision class `P`
is its specialization to functions with Boolean-valued output. No fixed
polynomial simulation overhead is claimed, only preservation of the class
of polynomial-time computable functions.
-/

namespace Lax51.TuringRamPolytimeEquivalence

open Lax51.RamPolytime Lax51.TuringPolytime

/-- **Polynomial-time machine invariance.** A total function on finite words
is computable in polynomial time by a uniform word RAM with a polynomially
bounded sufficient word length if and only if it is computable in polynomial
time by a finite multi-tape Turing machine. -/
axiom ramPolytime_iff_turingPolytime (f : List ℕ → List ℕ) :
  RamPolytime f ↔ TuringPolytime f

end Lax51.TuringRamPolytimeEquivalence
