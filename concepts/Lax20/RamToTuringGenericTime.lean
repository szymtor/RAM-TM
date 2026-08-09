import Lax20.RamPolytime
import Mathlib.Computability.TuringMachine.Computable

/-!
---
title: Generic-time simulation of word RAMs by Turing machines
type: theorem
---
An arbitrary finite execution of a fixed word-RAM program, using a word
length polynomially bounded in the encoded input size, can be simulated by
one finite multi-tape Turing machine.  The Turing running time has fixed
polynomial overhead in the encoded input size plus the number of executed
RAM instructions.

No regularity assumption is made on the RAM running time.  A polynomial word
length bound is retained because a Turing machine must explicitly process
the bits of every RAM word.
-/

namespace Lax20.RamToTuringGenericTime

open Lax13.Ram
open Lax20.BinaryWordEncoding Lax20.RamPolytime
open Polynomial Turing

/-- At a polynomially bounded selected word length, every `t`-step execution
of a fixed word-RAM program is simulated by one finite Turing machine in a
fixed polynomial of the input bit-size plus `t`. -/
axiom ramInTime_to_turingInPolynomialOverhead
    (p : Program) (wordBound : Polynomial ℕ) :
    ∃ (H : TM2ComputableAux Symbol Symbol)
        (widthOverhead timeOverhead : Polynomial ℕ),
      (∀ n, wordBound.eval n ≤ widthOverhead.eval n) ∧
        ∀ (x output : List ℕ) (t : ℕ),
          FitsInWords (wordBound.eval (bitSize x))
              ((x.length :: x) ++ output) →
            RunsTo (widthOverhead.eval (bitSize x)) p
                (x.length :: x) output t →
              Nonempty (TM2OutputsInTime H.tm
                (List.map H.inputAlphabet.invFun (encode x))
                (some (List.map H.outputAlphabet.invFun (encode output)))
                (timeOverhead.eval (bitSize x + t)))

end Lax20.RamToTuringGenericTime
