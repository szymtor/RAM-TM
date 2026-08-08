import Lax20Proofs.TMToRam.Polytime
import Lax20Proofs.RamToTM.Polytime
import Lax20.TuringRamPolytimeEquivalence

namespace Lax20Proofs.TuringRamPolytimeEquivalence

open Lax20.RamPolytime Lax20.TuringPolytime

/--
---
conclusion: Lax20.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime
---
**Polynomial-time machine invariance.** A total function on finite words
is computable in polynomial time by a finite multi-tape Turing machine if
and only if it is computable in polynomial time by a uniform word RAM with
a polynomially bounded sufficient word length. -/
theorem ramPolytime_iff_turingPolytime (f : List ℕ → List ℕ) :
    RamPolytime f ↔ TuringPolytime f := by
  constructor
  · exact Lax20Proofs.RamToTM.ramPolytime_to_turingPolytime
  · exact Lax20Proofs.TMToRam.turingPolytime_to_ramPolytime

end Lax20Proofs.TuringRamPolytimeEquivalence
