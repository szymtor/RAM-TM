import Lax13.Ram
import Lax51.BinaryWordEncoding
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.TuringMachine.Computable

/-!
---
title: Generic-time simulation of Turing machines by word RAMs
type: theorem
---
A finite multi-tape Turing-machine computation with an arbitrary numerical
per-input running-time bound can be simulated by one uniform word-RAM
program.  Both the sufficient word length and the RAM running time have
fixed polynomial overhead in the encoded input size plus the supplied
Turing running time.

No regularity assumption is made on the running-time function: it need not
be polynomial, monotone, or computable.  The result is therefore a generic
quantitative simulation theorem.  Computability and polynomial-time
preservation follow by separately imposing the corresponding regularity on
the supplied bound.
-/

namespace Lax51.TuringToRamGenericTime

open Lax13.Ram
open Lax51.BinaryWordEncoding
open Polynomial Turing

/-- A finite Turing machine with an arbitrary per-input numerical
running-time bound compiles to one uniform word-RAM program.  The sufficient
word length and RAM running time are fixed polynomials in the input bit-size
plus that bound. -/
axiom turingWithInputTime_to_ramInPolynomialOverhead
    {f : List ℕ → List ℕ}
    (H : TM2ComputableAux Symbol Symbol) (time : List ℕ → ℕ)
    (hrun : ∀ x, TM2OutputsInTime H.tm
      (List.map H.inputAlphabet.invFun (encode x))
      (some (List.map H.outputAlphabet.invFun (encode (f x)))) (time x)) :
    ∃ (p : Program) (wordOverhead timeOverhead : Polynomial ℕ),
      ∀ (x : List ℕ) (w : ℕ),
        wordOverhead.eval (bitSize x + time x) ≤ w →
          ∃ t ≤ timeOverhead.eval (bitSize x + time x),
            RunsTo w p (x.length :: x) (f x) t

end Lax51.TuringToRamGenericTime
