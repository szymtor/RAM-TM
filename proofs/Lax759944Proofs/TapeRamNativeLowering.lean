import Lax759944Proofs.TapeRamBufferedSimulation
import Lax759944Proofs.TapeRamBufferedLegacy

namespace Lax759944Proofs.TapeRamNativeLowering

/-- Lower every instruction of the current RAM on the native length-prefixed
input convention to the verified sequential-machine implementation. -/
def lower (program : Lax808846.Ram.Program) : Legacy.Ram.Program :=
  TapeRamBufferedLegacy.lower 1 program

/-- The complete native-input lowerer contract, including the counted input
snapshot and the one-bit enlargement separating virtual and scratch cells. -/
theorem runsTo (program : Lax808846.Ram.Program) (v : Nat)
    (input output : List Nat) (time : Nat)
    (hfit : ∀ value ∈ input.length :: input, value < 2 ^ v)
    (hcapacity : input.length + 33 < 2 ^ v)
    (hrun : Lax808846.Ram.RunsTo v program (input.length :: input) output time) :
    ∃ legacyTime ≤ 18 * time + 6 * (input.length + 1) + 26,
      Legacy.Ram.RunsTo (v + 1) (lower program)
        (input.length :: input) output legacyTime := by
  obtain ⟨physicalTime, htime, hphysical⟩ :=
    TapeRamBufferedSimulation.runsTo_compile (extra := 1)
      (header := input.length) (tail := input) (by simp) hfit (by simpa [Nat.add_assoc] using hcapacity) hrun
  obtain ⟨legacyTime, hlegacyTime, hlegacy⟩ := TapeRamBufferedLegacy.runsTo_lower hphysical
  exact ⟨legacyTime, hlegacyTime.trans htime, hlegacy⟩

end Lax759944Proofs.TapeRamNativeLowering
