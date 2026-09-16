import Lax759944Proofs.TapeRamVirtualSimulation

open Lax808846.Ram Lax759944Proofs.TapeRamVirtualCompiler

-- Include fetched terminal instructions, retaining both input views for comparison.
private def finish (w : Nat) (p : Program) : Nat → State → Option (Nat × State)
  | 0, _ => none
  | fuel + 1, s => match step w p s with
      | none => some (terminalCost p s, s)
      | some next => (finish w p fuel next).map fun (time, final) => (time + 1, final)

private def checkTranslation (label : String) (v : Nat) (p : Program)
    (input expected : List Nat) (expectedTime : Nat) : IO Unit := do
  let some (sourceTime, source) := finish v p 100 (initState input)
    | throw (IO.userError s!"{label}: source did not halt")
  let some (targetTime, target) := finish (v + 1) (compile p) 2000 (initState input)
    | throw (IO.userError s!"{label}: compiled program did not halt")
  unless source.out == expected && sourceTime == expectedTime do
    throw (IO.userError s!"{label}: bad fixture output {source.out}, time {sourceTime}")
  unless target.out == source.out && target.inp == source.inp && target.input == input do
    throw (IO.userError s!"{label}: output or input views changed")
  unless targetTime ≤ 18 * sourceTime + 21 do
    throw (IO.userError s!"{label}: compiled cost {targetTime} exceeds proved bound")

#eval checkTranslation "empty program" 3 [] [17] [] 0
#eval checkTranslation "explicit halt" 3 [.halt] [17] [] 1
#eval checkTranslation "exhausted read" 3 [.read 0] [] [] 1
#eval checkTranslation "input truncation" 3 [.read 0, .write 0, .halt] [127] [7] 3
#eval checkTranslation "sequential and indexed input" 3
  [.inputLength 0, .read 1, .set 2 1, .inputLoad 3 2, .inputLength 4,
    .write 0, .write 1, .write 3, .write 4, .halt] [9, 10] [2, 1, 2, 2] 10
#eval checkTranslation "aliased wrapped input index" 3
  [.set 1 9, .inputLoad 9 9, .write 1, .halt] [5, 23] [7] 4
#eval checkTranslation "original length exceeds virtual capacity" 3
  [.inputLength 0, .write 0, .set 1 7, .inputLoad 1 1, .write 1, .halt]
  (List.range 19) [3, 7] 6
#eval checkTranslation "indexed read outside input" 3
  [.set 0 7, .inputLoad 0 0, .write 0, .halt] [99] [0] 4
#eval checkTranslation "EOF branches with zero data" 3
  [.jeof 4, .read 0, .write 0, .jump 0, .halt] [0] [0] 6
#eval checkTranslation "EOF branch outside program" 3 [.jeof 500] [] [] 1
#eval checkTranslation "input remains indexed after exhaustion" 3
  [.read 0, .set 1 0, .inputLoad 1 1, .write 1, .inputLength 1, .write 1, .halt]
  [15] [7, 1] 7
#eval checkTranslation "indirect writes preserve input" 3
  [.set 0 7, .set 1 6, .store 0 1, .load 2 0, .inputLoad 3 0,
    .write 2, .write 7, .write 3, .halt] (List.range 8) [6, 6, 7] 9
#eval checkTranslation "virtual arithmetic wrap" 3
  [.set 0 7, .set 1 3, .add 2 0 1, .mul 3 0 1, .write 2, .write 3, .halt] [] [2, 5] 7

/-- info: 'Lax759944Proofs.TapeRamVirtualSimulation.runsTo_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax759944Proofs.TapeRamVirtualSimulation.runsTo_compile
