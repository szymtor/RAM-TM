import Lax759944Proofs.TMToRam.Polytime
import Lax759944Proofs.RamToTM.Polytime
import Lax759944.TuringRamPolytimeEquivalence

namespace Lax759944Proofs.TuringRamPolytimeEquivalence

open Lax759944.RamPolytime Lax759944.TuringPolytime

/--
---
conclusion: Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime
---
**Polynomial-time machine invariance.** A total function on finite words
is computable in polynomial time by a finite multi-tape Turing machine if
and only if it is computable in polynomial time by a uniform word RAM with
a polynomially bounded sufficient word length. -/
theorem ramPolytime_iff_turingPolytime (f : List ℕ → List ℕ) :
    RamPolytime f ↔ TuringPolytime f := by
  constructor
  · exact Lax759944Proofs.RamToTM.ramPolytime_to_turingPolytime
  · exact Lax759944Proofs.TMToRam.turingPolytime_to_ramPolytime

end Lax759944Proofs.TuringRamPolytimeEquivalence
