-- Historical predicate, used only by the legacy simulation proofs.
import Lax759944Proofs.Legacy.Ram
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
Turing machines and word random access machines compute exactly the same
total functions from finite lists of natural numbers to finite lists of
natural numbers.

A function is word-RAM computable when there are one program and a
computable word-length threshold, depending on the input, such that the
program returns the exact value from the length-prefixed physical input
`x.length :: x` at every word length at or above that threshold. The program
is chosen before both the input and the word length, so it is uniform.
Requiring the threshold to be computable is essential:
mere eventual stabilization with no effective modulus describes the larger
class of limit-computable functions.

On the Turing-machine side, `Computable` is mathlib's standard predicate for
total computability. Mathlib's Turing-machine development proves its
equivalence with execution by a concrete finitely described Turing machine,
so the right-hand side is the usual Turing-computability notion rather than
an additional machine model introduced here.

No running-time comparison is asserted. The theorem identifies the
functions computable by the two models; simulations may have arbitrary
overhead.
-/

namespace Lax759944Proofs.Legacy.TuringRamEquivalence

open Lax759944Proofs.Legacy.Ram

/-- A total function on finite words is computable by a word RAM if one
uniform program computes it from the length-prefixed physical input
`x.length :: x` at every effectively sufficient word length. -/
def RamComputable (f : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (threshold : List ℕ → ℕ),
    Computable threshold ∧
      ∀ (x : List ℕ) (w : ℕ), threshold x ≤ w →
        ∃ t : ℕ, RunsTo w p (x.length :: x) (f x) t

end Lax759944Proofs.Legacy.TuringRamEquivalence
