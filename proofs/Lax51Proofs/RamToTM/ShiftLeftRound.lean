import Lax51Proofs.RamToTM.ShiftCorePrimitives
import Lax51Proofs.RamToTM.PhaseComposition
import Lax51Proofs.RamToTM.UnifiedCleanLookup

namespace Lax51Proofs.RamToTM

open Turing TM2

def shiftRoundEncode : ShiftStack -> CoreStack
  | .source => .accumulator
  | .temp => .work5
  | .result => .work6

def shiftRoundDecode : CoreStack -> Option ShiftStack
  | .accumulator => some .source
  | .work5 => some .temp
  | .work6 => some .result
  | _ => none

def shiftRoundRenaming : StackRenaming ShiftStack CoreStack where
  encode := shiftRoundEncode
  decode := shiftRoundDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;>
      simp [shiftRoundDecode, shiftRoundEncode] at h ⊢

abbrev ShiftRoundFinalLabel (R : Type) := Sum SymbolMoveLabel R
abbrev ShiftLeftRoundTailLabel (R : Type) :=
  Sum SymbolMoveLabel (ShiftRoundFinalLabel R)
abbrev ShiftLeftRoundLabel (R : Type) :=
  Sum ShiftLabel (ShiftLeftRoundTailLabel R)

def shiftRoundFinalProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ShiftRoundFinalLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ShiftRoundFinalLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def shiftLeftRoundTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ShiftLeftRoundTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ShiftLeftRoundTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (shiftRoundFinalProgram returnLabel right)

def shiftLeftRoundProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ShiftLeftRoundLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ShiftLeftRoundLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft shiftRoundRenaming FullInterpreterState.shiftLens
      sparseShiftLeftCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (shiftLeftRoundTailProgram returnLabel right)

def shiftRoundStacks (word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits (fuel.length + 1) word).map SparseSymbol.bit
  | .work1 => fuel
  | .work3 => (fixedBits (fuel.length + 1) count).map SparseSymbol.bit
  | .memory => encodeSparseMemory (fuel.length + 1) m ++ [.memoryEnd]
  | .work0 | .work2 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def shiftRoundBase (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w word).map SparseSymbol.bit
  | .work1 => fuel
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 | .work2 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def shiftAfterCoreStacks (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    CoreStack -> List SparseSymbol
  | .work6 => (shiftLeftBits (fixedBits w word)).map SparseSymbol.bit
  | .work1 => fuel
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .accumulator | .work0 | .work2 | .work4 | .work5 | .work7 => []
  | k => base k

def shiftAfterFirstMoveStacks (w word count : Nat)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .work0 => (shiftLeftBits (fixedBits w word)).reverse.map SparseSymbol.bit
  | .work1 => fuel
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .accumulator | .work2 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem shiftLeft_core_bridge {N : Nat} {R : Type}
    (w word count : Nat) (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    phaseReturnCfg shiftRoundRenaming FullInterpreterState.shiftLens
      (Sum.inl SymbolMoveLabel.loop : ShiftLeftRoundTailLabel R)
      (sparseShiftLeftLocalCfg .done [] []
        (shiftLeftBits (fixedBits w word)))
      state (shiftRoundBase w word count fuel m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((shiftLeftBits (fixedBits w word)).map SparseSymbol.bit) [])
      (FullInterpreterState.shiftLens.put state default)
      (shiftAfterCoreStacks w word count fuel m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, shiftRoundRenaming,
    shiftRoundDecode, sparseShiftLeftLocalCfg, sparseShiftCfg, shiftCfg,
    shiftStacks, mapAlphabetCfg, mapAlphabetStacks, sparseBitEncode,
    shiftRoundBase, shiftAfterCoreStacks, renamedStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks]
  constructor
  · rw [show ({ held := none } : MoveControl) = default by rfl]
    have hm : FullInterpreterState.moveLens.get
        (FullInterpreterState.shiftLens.put state default) = default := by
      simpa using hmove
    rw [← hm, FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [shiftRoundBase, shiftAfterCoreStacks, renamedStacks,
      shiftRoundRenaming, shiftRoundDecode, sparseShiftLeftLocalCfg,
      sparseShiftCfg, shiftCfg, shiftStacks, mapAlphabetCfg,
      mapAlphabetStacks, sparseBitEncode, symbolMoveCoreRenaming,
      symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks]

theorem shiftLeft_firstMove_bridge {N : Nat} {R : Type}
    (w word count : Nat) (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl SymbolMoveLabel.loop : ShiftRoundFinalLabel R)
      (symbolMoveLocalCfg .done []
        ((shiftLeftBits (fixedBits w word)).map SparseSymbol.bit).reverse)
      state (shiftAfterCoreStacks w word count fuel m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((shiftLeftBits (fixedBits w word)).map SparseSymbol.bit).reverse [])
      (FullInterpreterState.moveLens.put state default)
      (shiftAfterFirstMoveStacks w word count fuel m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, shiftAfterCoreStacks,
    shiftAfterFirstMoveStacks, renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks]
  constructor
  · rfl
  · funext k
    cases k <;> simp [shiftAfterCoreStacks, shiftAfterFirstMoveStacks,
      renamedStacks, symbolMoveCoreRenaming, symbolMoveCoreDecode,
      symbolMoveLocalCfg, symbolMoveStacks]

theorem shiftLeft_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens returnLabel
      (symbolMoveLocalCfg .done []
        ((shiftLeftBits (fixedBits w word)).map SparseSymbol.bit).reverse.reverse)
      state (shiftAfterFirstMoveStacks w word count fuel m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (shiftRoundBase w (2 * word) count fuel m base) := by
  simp [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    shiftAfterFirstMoveStacks, shiftRoundBase, renamedStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, shiftLeftBits_fixed, List.map_reverse]
  funext k
  cases k <;> simp [shiftAfterFirstMoveStacks, shiftRoundBase,
    renamedStacks, symbolMoveCoreRenaming, symbolMoveCoreDecode,
    symbolMoveLocalCfg, symbolMoveStacks, shiftLeftBits_fixed]

theorem shiftLeftRound_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w word count : Nat) (hw : 0 < w) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (shiftLeftRoundProgram returnLabel right)))^[4 * w + 8])
        (some (lensRenamedCfg shiftRoundRenaming
          FullInterpreterState.shiftLens
          (sparseShiftLeftLocalCfg .first (fixedBits w word) [] [])
          state (shiftRoundBase w word count fuel m base))) =
      some (mapLabelCfg (fun l : ShiftLeftRoundTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l : ShiftRoundFinalLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (shiftRoundBase w (2 * word) count fuel m base))))) := by
  cases w with
  | zero => omega
  | succ w =>
      have hcore := run_lensPhase_to_right shiftRoundRenaming
        FullInterpreterState.shiftLens sparseShiftLeftCoreProgram .done (by rfl)
        (Sum.inl SymbolMoveLabel.loop) (shiftLeftRoundTailProgram returnLabel right)
        (sparseShiftLeftLocal_correct_nonempty
          (Nat.bodd word) (fixedBits w word.div2)) rfl state
        (shiftRoundBase (w + 1) word count fuel m base)
      rw [show Nat.bodd word :: fixedBits w word.div2 =
        fixedBits (w + 1) word by rfl] at hcore
      simp only [fixedBits_length] at hcore
      rw [shiftLeft_core_bridge (R := R) (w + 1) word count fuel m base state
        hmove] at hcore
      let coreState := FullInterpreterState.shiftLens.put state default
      have hfirst := run_lensPhase_to_right
        (symbolMoveCoreRenaming .work6 .work0 (by decide))
        FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
        (Sum.inl SymbolMoveLabel.loop) (shiftRoundFinalProgram returnLabel right)
        (symbolMoveLocal_correct
          ((shiftLeftBits (fixedBits (w + 1) word)).map SparseSymbol.bit) [])
        rfl coreState (shiftAfterCoreStacks (w + 1) word count fuel m base)
      simp only [shiftLeftBits_length, fixedBits_length, List.length_map,
        List.append_nil] at hfirst
      rw [shiftLeft_firstMove_bridge (R := R) (w + 1) word count fuel m base
        coreState] at hfirst
      let firstState := FullInterpreterState.moveLens.put coreState default
      have hsecond := run_lensPhase_to_right
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
        returnLabel right
        (symbolMoveLocal_correct
          ((shiftLeftBits (fixedBits (w + 1) word)).map SparseSymbol.bit).reverse [])
        rfl firstState
        (shiftAfterFirstMoveStacks (w + 1) word count fuel m base)
      simp only [List.length_reverse, List.length_map, shiftLeftBits_length,
        fixedBits_length, List.append_nil] at hsecond
      rw [shiftLeft_return_bridge returnLabel (w + 1) word count fuel m base
        firstState] at hsecond
      have htail := chain_liftRightProgram
        (lensPhaseLeft
          (symbolMoveCoreRenaming .work6 .work0 (by decide))
          FullInterpreterState.moveLens symbolMoveCoreProgram .done
          (Sum.inl SymbolMoveLabel.loop))
        (shiftRoundFinalProgram returnLabel right) hfirst hsecond
      dsimp [coreState] at htail
      have hall := chain_liftRightProgram
        (lensPhaseLeft shiftRoundRenaming FullInterpreterState.shiftLens
          sparseShiftLeftCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
        (shiftLeftRoundTailProgram returnLabel right) hcore htail
      refine ⟨FullInterpreterState.moveLens.put firstState default, ?_⟩
      simpa [shiftLeftRoundProgram,
        show 4 * (w + 1) + 8 = (2 * (w + 1) + 4) +
          ((w + 1 + 2) + (w + 1 + 2)) by omega] using hall

end Lax51Proofs.RamToTM
