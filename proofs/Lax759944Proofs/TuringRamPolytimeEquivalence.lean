import Lax759944Proofs.TMToRam.Polytime
import Lax759944Proofs.RamToTM.Polytime
import Lax759944.TuringRamPolytimeEquivalence
import Lax759944Proofs.LegacyRamBridge
import Lax759944Proofs.LegacyRamClasses
import Lax759944Proofs.TapeRamNativeLowering

namespace Lax759944Proofs.TuringRamPolytimeEquivalence

open Lax759944Proofs.Legacy.RamPolytime Lax759944.TuringPolytime

/-- Polynomial-time equivalence for the historical instruction set, retained
as a reusable proof helper for the sequential-machine intermediate. -/
theorem legacyRamPolytime_iff_turingPolytime (f : List ℕ → List ℕ) :
    RamPolytime f ↔ TuringPolytime f := by
  constructor
  · exact Lax759944Proofs.RamToTM.ramPolytime_to_turingPolytime
  · exact Lax759944Proofs.TMToRam.turingPolytime_to_ramPolytime

/-- Every polynomial-time Turing computation runs on the current RAM.
The additional constant accounts for the fetched terminal instruction. -/
theorem turingPolytime_to_ramPolytime {f : List ℕ → List ℕ}
    (hf : TuringPolytime f) : Lax759944.RamPolytime.RamPolytime f := by
  obtain ⟨p, wordBound, timeBound, hp⟩ :=
    Lax759944Proofs.TMToRam.turingPolytime_to_ramPolytime hf
  refine ⟨LegacyRamBridge.embedProgram p, wordBound, timeBound + 1, ?_⟩
  intro x
  refine ⟨(hp x).1, ?_⟩
  intro w hw
  obtain ⟨t, ht, hr⟩ := (hp x).2 w hw
  obtain ⟨u, _, hu, hr'⟩ := LegacyRamBridge.runsTo hr
  refine ⟨u, ?_, hr'⟩
  simpa using hu.trans (Nat.add_le_add_right ht 1)

/-- Buffer the native input during the measured run, then apply the verified
sequential-machine simulation to every instruction of the current RAM. -/
theorem ramPolytime_to_turingPolytime {f : List ℕ → List ℕ}
    (hf : Lax759944.RamPolytime.RamPolytime f) : TuringPolytime f := by
  apply Lax759944Proofs.RamToTM.ramPolytime_to_turingPolytime
  exact LegacyRamClasses.polytime_backward_of_lowering TapeRamNativeLowering.lower
    TapeRamNativeLowering.runsTo hf Encoding.length_le_bitSize

/--
---
conclusion: Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime
---
The forward simulation covers the full current instruction set, including
indexed input, input length, and EOF. The reverse simulation uses the checked
instruction embedding, with both terminal-instruction costs accounted for.
-/
theorem ramPolytime_iff_turingPolytime (f : List ℕ → List ℕ) :
    Lax759944.RamPolytime.RamPolytime f ↔ TuringPolytime f :=
  ⟨ramPolytime_to_turingPolytime, turingPolytime_to_ramPolytime⟩

end Lax759944Proofs.TuringRamPolytimeEquivalence
