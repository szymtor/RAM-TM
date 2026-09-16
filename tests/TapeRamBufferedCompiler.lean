import Lax759944Proofs.TapeRamBufferedLegacy
import Lax759944Proofs.TapeRamBufferedSimulation

open Lax808846.Ram
open Lax759944Proofs

private def haltOutput (w : Nat) (p : Program) : Nat → State → Option (List Nat)
  | 0, _ => none
  | fuel + 1, s =>
      match step w p s with
      | none => some s.out
      | some next => haltOutput w p fuel next

private def agrees (extra : Nat) (p : Program) (input expected : List Nat) : Bool :=
  haltOutput 7 p 2048 (initState input) == some expected &&
    haltOutput 8 (TapeRamBufferedCompiler.compile extra p) 2048 (initState input) ==
      some expected

-- Indexed input remains available after consuming one sequential word.
#guard agrees 1 [.inputLength 0, .write 0, .read 0, .write 0,
  .inputLoad 0 0, .write 0] [2, 0, 9] [3, 2, 9]

-- Zero is data; EOF branches only after all three supplied words are read.
private def scan : Program :=
  [.jeof 3, .read 0, .jump 0, .inputLength 0, .write 0,
   .inputLoad 0 0, .write 0, .halt]
#guard agrees 1 scan [2, 0, 9] [3, 0]
#guard agrees 1 scan [0] [1, 0]
#guard agrees 4 scan [0, 0, 0, 0] [4, 0]

-- An exhausted read terminates before the following write.
#guard agrees 1 [.read 0, .read 1, .read 2, .read 3, .write 0] [2, 0, 9] []

-- Virtual address reduction and destination/index aliasing both matter.
#guard agrees 1 [.set 130 2, .inputLoad 130 130, .write 130] [2, 0, 9] [9]
#guard agrees 1 [.set 0 127, .inputLoad 0 0, .write 0] [2, 0, 9] [0]

-- Both forms of termination and the empty program preserve exact output.
#guard agrees 1 [] [0] []
#guard agrees 1 [.halt] [0] []
#guard agrees 1 [.jump 99] [0] []

example (extra : Nat) (p : Program) :
    LegacyRamBridge.embedProgram (TapeRamBufferedLegacy.lower extra p) =
      TapeRamBufferedCompiler.compile extra p :=
  TapeRamBufferedLegacy.embed_lower extra p

#print axioms TapeRamBufferedLegacy.runsTo_lower

/-- info: 'Lax759944Proofs.TapeRamBufferedSimulation.runsTo_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax759944Proofs.TapeRamBufferedSimulation.runsTo_compile
