import Lax13.Ram
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
---
title: Equivalence of Turing machines and word RAMs
type: theorem
---
Turing machines and word random access machines compute exactly the same
total functions from finite lists of natural numbers to finite lists of
natural numbers.

A function is word-RAM computable when there are one program and a
computable word-length threshold, depending on the input, such that the
program returns the exact value at every word length at or above that
threshold. The program is chosen before both the input and the word length,
so it is uniform. Requiring the threshold to be computable is essential:
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

namespace Lax20.TuringRamEquivalence

open Lax13.Ram

/-- A total function on finite words is computable by a word RAM if one
uniform program computes it exactly at every effectively sufficient word
length. -/
def RamComputable (f : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (threshold : List ℕ → ℕ),
    Computable threshold ∧
      ∀ (x : List ℕ) (w : ℕ), threshold x ≤ w →
        ∃ t : ℕ, RunsTo w p x (f x) t

/-- **Equivalence of Turing machines and word RAMs.** A total function on
finite words is computable by the archive's word RAM model exactly when it
is Turing-computable. -/
axiom ramComputable_iff_computable (f : List ℕ → List ℕ) :
  RamComputable f ↔ Computable f

end Lax20.TuringRamEquivalence
