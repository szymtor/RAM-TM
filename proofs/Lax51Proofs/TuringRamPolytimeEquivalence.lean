import Lax51Proofs.TMToRam.Polytime
import Lax51Proofs.RamToTM.Polytime
import Lax51.TuringRamPolytimeEquivalence

namespace Lax51Proofs.TuringRamPolytimeEquivalence

open Lax51.RamPolytime Lax51.TuringPolytime

/--
---
conclusion: Lax51.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime
---
**Polynomial-time machine invariance.** A total function on finite words
is computable in polynomial time by a finite multi-tape Turing machine if
and only if it is computable in polynomial time by a uniform word RAM with
a polynomially bounded sufficient word length. -/
theorem ramPolytime_iff_turingPolytime (f : List ℕ → List ℕ) :
    RamPolytime f ↔ TuringPolytime f := by
  constructor
  · exact Lax51Proofs.RamToTM.ramPolytime_to_turingPolytime
  · exact Lax51Proofs.TMToRam.turingPolytime_to_ramPolytime

end Lax51Proofs.TuringRamPolytimeEquivalence
