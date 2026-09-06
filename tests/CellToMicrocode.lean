import Lax51Proofs.CellToMicrocode

open Lax51Proofs

-- Reading, fixed-width complement, writing, and halting.
private def complementProgram : Lax13.Ram.Program :=
  [.read 0, .not 1 0, .write 1, .halt]

#guard (Lax13.Ram.run 3 complementProgram 3
  (Lax13.Ram.initState [5])).map Lax13.Ram.State.out == some [2]
#guard (Microcode.run 3 (CellToMicrocode.compile complementProgram) 9
  (Microcode.initState [5])).map Microcode.State.out == some [2]

-- At width zero every address aliases and every produced word is zero.
#guard (Lax13.Ram.run 0 complementProgram 3
  (Lax13.Ram.initState [5])).map Lax13.Ram.State.out == some [0]
#guard (Microcode.run 0 (CellToMicrocode.compile complementProgram) 9
  (Microcode.initState [5])).map Microcode.State.out == some [0]

-- Exhausted reads and missing instructions halt immediately in both models.
#guard (Lax13.Ram.step 3 complementProgram (Lax13.Ram.initState [])).isNone
#guard (Microcode.step 3 (CellToMicrocode.compile complementProgram)
  (Microcode.initState [])).isNone
#guard (Lax13.Ram.step 3 [] (Lax13.Ram.initState [5])).isNone
#guard (Microcode.step 3 (CellToMicrocode.compile []) (Microcode.initState [5])).isNone

-- Both outcomes of a conditional jump must land at a block boundary.
private def branchProgram : Lax13.Ram.Program :=
  [.read 0, .jzero 0 4, .set 1 7, .jump 5, .set 1 3, .write 1, .halt]

#guard (Microcode.run 4 (CellToMicrocode.compile branchProgram) 12
  (Microcode.initState [0])).map Microcode.State.out == some [3]
#guard (Microcode.run 4 (CellToMicrocode.compile branchProgram) 15
  (Microcode.initState [1])).map Microcode.State.out == some [7]

-- Oversized addresses and literals are normalized by the public model.
private def aliasProgram : Lax13.Ram.Program :=
  [.set 8 13, .not 0 8, .write 8, .halt]

#guard (Lax13.Ram.run 3 aliasProgram 3
  (Lax13.Ram.initState [])).map Lax13.Ram.State.out == some [2]
#guard (Microcode.run 3 (CellToMicrocode.compile aliasProgram) 9
  (Microcode.initState [])).map Microcode.State.out == some [2]

-- This theorem quantifies over all instructions, all widths (including zero),
-- arbitrary input words, and every finite halting execution.
example {w t : Nat} {p : Lax13.Ram.Program} {input output : List Nat}
    (h : Lax13.Ram.RunsTo w p input output t) :
    Microcode.RunsTo w (CellToMicrocode.compile p) input output (3 * t) :=
  CellToMicrocode.runsTo h

#print axioms CellToMicrocode.runsTo
#print axioms CellToMicrocode.polytime
#print axioms CellToMicrocode.computable
