import Lax759944Proofs.Computability.TapeRamComputable

open Lax808846.Ram
open Lax759944Proofs.Computability.TapeRam

-- Search counts successful transitions separately from terminal instruction cost.
#guard candidateAt [] 0 [] 0 == some []
#guard candidateAt [.halt] 0 [] 0 == some []
#guard candidateAt [.read 0, .read 0] 0 [] 1 == some []

-- Read the explicit framing word, retain immutable indexed input, and branch
-- on EOF after consuming the remaining word. Zero is ordinary input data.
private def tapeProgram : Program :=
  [.read 0, .inputLength 1, .inputLoad 2 0, .write 1, .write 2,
   .jeof 8, .read 0, .jeof 9, .halt, .halt]

#guard candidateAt tapeProgram 3 [5] 8 == some [2, 5]
#guard candidateAt tapeProgram 3 [0] 8 == some [2, 0]
#guard candidateAt tapeProgram 3 [5] 7 == none

-- An index is read before its destination is overwritten, even at aliases.
private def aliasProgram : Program := [.read 0, .inputLoad 0 0, .write 0, .halt]
#guard candidateAt aliasProgram 3 [5] 3 == some [5]
#guard candidateAt aliasProgram 0 [5] 3 == some [0]

-- Out-of-range indices return zero and indexed access leaves the tape intact.
private def outsideProgram : Program := [.set 0 7, .inputLoad 0 0, .write 0, .halt]
#guard candidateAt outsideProgram 3 [5] 3 == some [0]
#guard (execute 3 outsideProgram 3 (initial [1, 5])).map Config.inp == some [1, 5]

example (w : ℕ) (i : Instr) (s : Config) :
    (effect w i s).map Config.toState = i.effect w s.toState := effect_toState w i s

#print axioms effect_toState
#print axioms execute_toState
#print axioms candidateAt_primrec
#print axioms ramComputable_to_computable
