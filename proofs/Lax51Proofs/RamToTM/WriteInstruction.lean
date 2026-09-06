import Lax51Proofs.RamToTM.MultiplyInstruction

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

inductive WriteResetLabel | reset
  deriving DecidableEq, Fintype, Inhabited
inductive WriteFinishLabel | finish
  deriving DecidableEq, Fintype, Inhabited

abbrev WriteAfterLabel (R : Type) := Sum WriteFinishLabel R
abbrev WriteMove2Label (R : Type) := Sum SymbolMoveLabel (WriteAfterLabel R)
abbrev WriteMove1Label (R : Type) := Sum SymbolMoveLabel (WriteMove2Label R)
abbrev WriteTailLabel (R : Type) := Sum WriteResetLabel (WriteMove1Label R)
abbrev WriteInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (WriteTailLabel R)

def writeResultBase (w accumulator value : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .output => .wordEnd ::
      (fixedBits w value).reverse.map SparseSymbol.bit ++ base .output
  | .work0 | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def writeFinishProgram {N : Nat} {R : Type} (returnLabel : R) :
    WriteFinishLabel -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (WriteAfterLabel R) (FullInterpreterState N)
  | .finish => .push .output (fun _ => .wordEnd) <|
      .goto fun _ => Sum.inr returnLabel

def writeAfterProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram (writeFinishProgram returnLabel) right

def writeMove2Program {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram
    (lensPhaseLeft (symbolMoveCoreRenaming .work1 .output (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl WriteFinishLabel.finish))
    (writeAfterProgram returnLabel right)

def writeMove1Program {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram
    (lensPhaseLeft (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (writeMove2Program returnLabel right)

def writeResetProgram {N : Nat} {R : Type} : WriteResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (WriteTailLabel R) (FullInterpreterState N)
  | .reset => .load (fun s => FullInterpreterState.moveLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl SymbolMoveLabel.loop)

def writeTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram writeResetProgram (writeMove1Program returnLabel right)

def writeInstructionProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  operandEvalProgram o (Sum.inl WriteResetLabel.reset)
    (writeTailProgram returnLabel right)

def writeMove1Base (w accumulator value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) :=
  operandResultBase w accumulator value m base

def writeMove2Base (w accumulator value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work1 => (fixedBits w value).map SparseSymbol.bit
  | .work0 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def writeBeforeFinishBase (w accumulator value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .output => (fixedBits w value).reverse.map SparseSymbol.bit ++ base .output
  | .work0 | .work1 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem writeReset_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    ((fun o => o.bind (TM2.step (writeTailProgram returnLabel right)))^[1])
      (some (cleanReturnCfg (Sum.inl WriteResetLabel.reset) state
        (operandResultBase w accumulator value m base))) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        FullInterpreterState.moveLens
        (symbolMoveLocalCfg .loop
          ((fixedBits w value).reverse.map SparseSymbol.bit) [])
        (FullInterpreterState.moveLens.put state default)
        (writeMove1Base w accumulator value m base))) := by
  simp [writeTailProgram, writeResetProgram, cleanReturnCfg, liftRightProgram,
    mapLabelCfg, TM2.step, lensRenamedCfg, writeMove1Base,
    operandResultBase, renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
      symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
      operandResultBase, writeMove1Base]

theorem writeMove1_bridge {N : Nat} {R : Type}
    (w accumulator value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl SymbolMoveLabel.loop : WriteMove2Label R)
      (symbolMoveLocalCfg .done []
        ((fixedBits w value).map SparseSymbol.bit))
      state (writeMove1Base w accumulator value m base) =
    lensRenamedCfg (symbolMoveCoreRenaming .work1 .output (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((fixedBits w value).map SparseSymbol.bit) (base .output))
      (FullInterpreterState.moveLens.put state default)
      (writeMove2Base w accumulator value m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, writeMove1Base, writeMove2Base,
    operandResultBase, renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks]
  constructor
  · rfl
  · funext k
    cases k <;> simp [writeMove1Base, writeMove2Base, operandResultBase,
      renamedStacks, symbolMoveCoreRenaming, symbolMoveCoreDecode,
      symbolMoveLocalCfg, symbolMoveStacks]

theorem writeMove2_finish_bridge {N : Nat} {R : Type}
    (w accumulator value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg (symbolMoveCoreRenaming .work1 .output (by decide))
      FullInterpreterState.moveLens
      (Sum.inl WriteFinishLabel.finish : WriteAfterLabel R)
      (symbolMoveLocalCfg .done []
        (((fixedBits w value).map SparseSymbol.bit).reverse ++ base .output))
      state (writeMove2Base w accumulator value m base) =
    cleanReturnCfg (Sum.inl WriteFinishLabel.finish)
      (FullInterpreterState.moveLens.put state default)
      (writeBeforeFinishBase w accumulator value m base) := by
  simp [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    writeMove2Base, writeBeforeFinishBase, renamedStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks]
  funext k
  cases k <;> simp [writeMove2Base, writeBeforeFinishBase,
    renamedStacks, symbolMoveCoreRenaming, symbolMoveCoreDecode,
    symbolMoveLocalCfg, symbolMoveStacks]

theorem writeFinish_step {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    TM2.step (writeAfterProgram returnLabel right)
      (cleanReturnCfg (Sum.inl WriteFinishLabel.finish) state
        (writeBeforeFinishBase w accumulator value m base)) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel state
        (writeResultBase w accumulator value m base))) := by
  simp [writeAfterProgram, writeFinishProgram, cleanReturnCfg,
    liftRightProgram, TM2.step, mapLabelCfg, writeBeforeFinishBase,
    writeResultBase, Function.update]
  congr 2
  funext k
  cases k <;> simp [writeBeforeFinishBase, writeResultBase, Function.update]

theorem writeTail_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    ∃ finalState,
      ((fun o => o.bind (TM2.step (writeTailProgram returnLabel right)))^[
        2 * w + 6])
        (some (cleanReturnCfg (Sum.inl WriteResetLabel.reset) state
          (operandResultBase w accumulator value m base))) =
      some (mapLabelCfg (fun l : WriteMove1Label R => Sum.inr l)
        (mapLabelCfg (fun l : WriteMove2Label R => Sum.inr l)
          (mapLabelCfg (fun l : WriteAfterLabel R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (writeResultBase w accumulator value m base)))))) := by
  have h0 := writeReset_correct returnLabel right w accumulator value m base state
  simp only [List.map_reverse] at h0
  let state0 := FullInterpreterState.moveLens.put state default
  have h1 := run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .work1 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (writeMove2Program returnLabel right)
    (symbolMoveLocal_correct
      ((fixedBits w value).reverse.map SparseSymbol.bit) []) rfl
    state0 (writeMove1Base w accumulator value m base)
  simp only [List.length_map, List.length_reverse, fixedBits_length,
    List.append_nil, List.map_reverse, List.reverse_reverse] at h1
  rw [writeMove1_bridge (R := R) w accumulator value m base state0] at h1
  let state1 := FullInterpreterState.moveLens.put state0 default
  have h2 := run_lensPhase_to_right
    (symbolMoveCoreRenaming .work1 .output (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl WriteFinishLabel.finish) (writeAfterProgram returnLabel right)
    (symbolMoveLocal_correct ((fixedBits w value).map SparseSymbol.bit)
      (base .output)) rfl
    state1 (writeMove2Base w accumulator value m base)
  simp only [List.length_map, fixedBits_length, List.map_reverse] at h2
  rw [writeMove2_finish_bridge (R := R) w accumulator value m base state1] at h2
  have h3 :
      ((fun o => o.bind (TM2.step (writeAfterProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl WriteFinishLabel.finish)
          (FullInterpreterState.moveLens.put state1 default)
          (writeBeforeFinishBase w accumulator value m base))) =
      some (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel
          (FullInterpreterState.moveLens.put state1 default)
          (writeResultBase w accumulator value m base))) := by
    simpa using writeFinish_step returnLabel right w accumulator value m base
      (FullInterpreterState.moveLens.put state1 default)
  have h23 := chain_liftRightProgram
    (lensPhaseLeft (symbolMoveCoreRenaming .work1 .output (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl WriteFinishLabel.finish))
    (writeAfterProgram returnLabel right) h2 h3
  have h123 := chain_liftRightProgram
    (lensPhaseLeft (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (writeMove2Program returnLabel right) h1 h23
  have h := chain_liftRightProgram writeResetProgram
    (writeMove1Program returnLabel right) h0 h123
  refine ⟨FullInterpreterState.moveLens.put state1 default, ?_⟩
  have htime : 2 * w + 6 = 1 + ((w + 2) + ((w + 2) + 1)) := by omega
  rw [htime]
  simpa [writeTailProgram, writeMove1Program, writeMove2Program,
    state0, state1] using h

def writeInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 2 * w + 6

theorem writeInstruction_correct {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator : Nat) (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= writeInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (writeInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg (R := WriteTailLabel R)
          o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l : WriteMove1Label R => Sum.inr l)
          (mapLabelCfg (fun l : WriteMove2Label R => Sum.inr l)
            (mapLabelCfg (fun l : WriteAfterLabel R => Sum.inr l)
              (mapLabelCfg (fun l : R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (writeResultBase w accumulator
                    (operandWordValue w o m) m base))))))) := by
  rcases operandEval_correct o hN w accumulator m hm
      (Sum.inl WriteResetLabel.reset) (writeTailProgram returnLabel right)
      state base with ⟨operandSteps, operandBound, operandState, hoperand⟩
  rcases writeTail_correct returnLabel right w accumulator
      (operandWordValue w o m) m base operandState with
    ⟨writeState, hwrite⟩
  have hlift := transport_iterate_operand_right o
    (Sum.inl WriteResetLabel.reset) (writeTailProgram returnLabel right) hwrite
  have hchain := chain_loadInstruction_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (WriteInstructionLabel o R) (FullInterpreterState N)) =>
      x.bind (TM2.step (writeInstructionProgram o returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (2 * w + 6), ?_, writeState, ?_⟩
  · simp [writeInstructionBound]
    omega
  · simpa [writeInstructionProgram] using hchain

theorem encodeOutputStack_append_one (w : Nat) (out : List Nat) (value : Nat) :
    encodeOutputStack w (out ++ [value]) =
      .wordEnd :: (fixedBits w value).reverse.map SparseSymbol.bit ++
        encodeOutputStack w out := by
  simp [encodeOutputStack, encodeWordList, encodeFixedWord,
    List.reverse_append, List.map_reverse, List.append_assoc]

theorem writeResultBase_coreStacks (w value : Nat) (s : SparseState) :
    writeResultBase w s.acc value s.mem (coreStacks w s) =
      coreStacks w { s with out := s.out ++ [value] } := by
  funext k
  cases k <;> simp [writeResultBase, coreStacks, encodeMemoryStack,
    encodeAccumulator, encodeOutputStack_append_one]

end Lax51Proofs.RamToTM
