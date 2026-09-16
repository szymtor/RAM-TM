import Lax759944Proofs.LegacyRamBridge

open Lax759944Proofs.LegacyRamBridge

private def legacyProgram : Lax759944Proofs.Legacy.Ram.Program :=
  [.read 0, .not 1 0, .write 1, .halt]

-- A complete output is preserved, including width zero and address aliasing.
#guard (Lax808846.Ram.run 3 (embedProgram legacyProgram) 3
  (Lax808846.Ram.initState [5])).map Lax808846.Ram.State.out == some [2]
#guard (Lax808846.Ram.run 0 (embedProgram legacyProgram) 3
  (Lax808846.Ram.initState [5])).map Lax808846.Ram.State.out == some [0]

-- No instruction is fetched by an empty program. Explicit halt and exhausted
-- read each cost one, even though neither makes a successful transition.
example : Lax808846.Ram.RunsTo 0 [] [] [] 0 :=
  ⟨0, Lax808846.Ram.initState [], rfl, rfl, rfl, rfl⟩
example : Lax808846.Ram.RunsTo 0 [.halt] [] [] 1 :=
  ⟨0, Lax808846.Ram.initState [], rfl, rfl, rfl, rfl⟩
example : Lax808846.Ram.RunsTo 0 [.read 0] [] [] 1 :=
  ⟨0, Lax808846.Ram.initState [], rfl, rfl, rfl, rfl⟩

-- Indexed reads address the immutable original input after sequential reads.
private def indexedProgram : Lax808846.Ram.Program :=
  [.read 0, .inputLength 1, .inputLoad 2 0, .write 2, .halt]

#guard (Lax808846.Ram.run 3 indexedProgram 4
  (Lax808846.Ram.initState [1, 7])).map Lax808846.Ram.State.out == some [7]
#guard (Lax808846.Ram.run 3 indexedProgram 4
  (Lax808846.Ram.initState [1, 7])).map Lax808846.Ram.State.input == some [1, 7]
#guard (Lax808846.Ram.run 3 indexedProgram 4
  (Lax808846.Ram.initState [1, 7])).map Lax808846.Ram.State.inp == some [7]
#guard (Lax808846.Ram.run 3 indexedProgram 4
  (Lax808846.Ram.initState [1, 7])).map (fun s => s.mem 1) == some 2

-- Zero remains ordinary data. EOF detection does not consume it.
private def eofProgram : Lax808846.Ram.Program :=
  [.jeof 3, .read 0, .write 0, .halt]

#guard (Lax808846.Ram.run 3 eofProgram 3
  (Lax808846.Ram.initState [0])).map Lax808846.Ram.State.out == some [0]
#guard (Lax808846.Ram.run 3 eofProgram 1
  (Lax808846.Ram.initState [])).map Lax808846.Ram.State.pc == some 3

-- General preservation quantifies over every program, width, and input.
example {w t : ℕ} {p : Lax759944Proofs.Legacy.Ram.Program}
    {input output : List ℕ}
    (h : Lax759944Proofs.Legacy.Ram.RunsTo w p input output t) :
    ∃ u, t ≤ u ∧ u ≤ t + 1 ∧
      Lax808846.Ram.RunsTo w (embedProgram p) input output u := runsTo h

#print axioms run_embed
#print axioms runsTo
#print axioms computesInTime
