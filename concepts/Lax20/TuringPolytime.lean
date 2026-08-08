import Lax20.BinaryWordEncoding
import Mathlib.Computability.TuringMachine.Computable

/-!
---
title: Polynomial-time computation by a Turing machine
type: definition
---
A total function from finite lists of natural numbers to finite lists of
natural numbers is Turing-computable in polynomial time when a finite
multi-tape Turing machine transforms the canonical binary encoding of every
input into the canonical binary encoding of its value within a polynomial
number of steps in the encoded input length.

The underlying machine and time bound are mathlib's
`Turing.TM2ComputableInPolyTime`: a bundled finite multi-stack Turing machine
and a polynomial over the natural numbers. Taking `Nonempty` forgets the
computational content of the bundle and retains the proposition that such a
machine exists.
-/

namespace Lax20.TuringPolytime

open Lax20.BinaryWordEncoding

/-- Polynomial-time computation, on the canonical binary word encoding, by
a finite multi-tape Turing machine. -/
def TuringPolytime (f : List ℕ → List ℕ) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encode encode f)

end Lax20.TuringPolytime
