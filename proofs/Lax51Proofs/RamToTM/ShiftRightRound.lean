import Lax51Proofs.RamToTM.ShiftLeftRound

namespace Lax51Proofs.RamToTM

open Turing TM2

abbrev ShiftRightRoundLabel (R : Type) :=
  Sum ShiftRightLabel (ShiftLeftRoundTailLabel R)

def shiftRightRoundProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ShiftRightRoundLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ShiftRightRoundLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft shiftRoundRenaming FullInterpreterState.shiftLens
      sparseShiftRightCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (shiftLeftRoundTailProgram returnLabel right)

def shiftRightAfterCoreStacks (w word count : Nat)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .work6 => (shiftRightBits (fixedBits w word)).map SparseSymbol.bit
  | .work1 => fuel
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .accumulator | .work0 | .work2 | .work4 | .work5 | .work7 => []
  | k => base k

def shiftRightAfterFirstMoveStacks (w word count : Nat)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .work0 => (shiftRightBits (fixedBits w word)).reverse.map SparseSymbol.bit
  | .work1 => fuel
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .accumulator | .work2 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem shiftRight_core_bridge {N : Nat} {R : Type}
    (w word count : Nat) (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    phaseReturnCfg shiftRoundRenaming FullInterpreterState.shiftLens
      (Sum.inl SymbolMoveLabel.loop : ShiftLeftRoundTailLabel R)
      (sparseShiftRightLocalCfg .done [] []
        (shiftRightBits (fixedBits w word)))
      state (shiftRoundBase w word count fuel m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((shiftRightBits (fixedBits w word)).map SparseSymbol.bit) [])
      (FullInterpreterState.shiftLens.put state default)
      (shiftRightAfterCoreStacks w word count fuel m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, shiftRoundRenaming,
    shiftRoundDecode, sparseShiftRightLocalCfg, shiftRightCfg,
    shiftStacks, mapAlphabetCfg, mapAlphabetStacks, sparseBitEncode,
    shiftRoundBase, shiftRightAfterCoreStacks, renamedStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks]
  constructor
  · have hm : FullInterpreterState.moveLens.get
        (FullInterpreterState.shiftLens.put state default) = default := by
      simpa using hmove
    rw [← hm, FullInterpreterState.moveLens.put_get]
    rfl
  · funext k
    cases k <;> simp [shiftRoundBase, shiftRightAfterCoreStacks,
      renamedStacks, shiftRoundRenaming, shiftRoundDecode,
      sparseShiftRightLocalCfg, shiftRightCfg, shiftStacks,
      mapAlphabetCfg, mapAlphabetStacks, sparseBitEncode,
      symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
      symbolMoveStacks]

theorem shiftRight_firstMove_bridge {N : Nat} {R : Type}
    (w word count : Nat) (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl SymbolMoveLabel.loop : ShiftRoundFinalLabel R)
      (symbolMoveLocalCfg .done []
        ((shiftRightBits (fixedBits w word)).map SparseSymbol.bit).reverse)
      state (shiftRightAfterCoreStacks w word count fuel m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((shiftRightBits (fixedBits w word)).map SparseSymbol.bit).reverse [])
      (FullInterpreterState.moveLens.put state default)
      (shiftRightAfterFirstMoveStacks w word count fuel m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, shiftRightAfterCoreStacks,
    shiftRightAfterFirstMoveStacks, renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks]
  constructor
  · rfl
  · funext k
    cases k <;> simp [shiftRightAfterCoreStacks,
      shiftRightAfterFirstMoveStacks, renamedStacks, symbolMoveCoreRenaming,
      symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks]

theorem shiftRight_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w word count : Nat) (fuel : List SparseSymbol)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) (hword : word < 2 ^ w) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens returnLabel
      (symbolMoveLocalCfg .done []
        ((shiftRightBits (fixedBits w word)).map SparseSymbol.bit).reverse.reverse)
      state (shiftRightAfterFirstMoveStacks w word count fuel m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (shiftRoundBase w (word / 2) count fuel m base) := by
  simp [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    shiftRightAfterFirstMoveStacks, shiftRoundBase, renamedStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, shiftRightBits_fixed w word hword, List.map_reverse]
  funext k
  cases k <;> simp [shiftRightAfterFirstMoveStacks, shiftRoundBase,
    renamedStacks, symbolMoveCoreRenaming, symbolMoveCoreDecode,
    symbolMoveLocalCfg, symbolMoveStacks, shiftRightBits_fixed w word hword]

theorem shiftRightRound_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w word count : Nat) (hw : 0 < w) (hword : word < 2 ^ w)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (shiftRightRoundProgram returnLabel right)))^[4 * w + 7])
        (some (lensRenamedCfg shiftRoundRenaming
          FullInterpreterState.shiftLens
          (sparseShiftRightLocalCfg .discard (fixedBits w word) [] [])
          state (shiftRoundBase w word count fuel m base))) =
      some (mapLabelCfg (fun l : ShiftLeftRoundTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l : ShiftRoundFinalLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (shiftRoundBase w (word / 2) count fuel m base))))) := by
  cases w with
  | zero => omega
  | succ w =>
      have hcore := run_lensPhase_to_right shiftRoundRenaming
        FullInterpreterState.shiftLens sparseShiftRightCoreProgram .done (by rfl)
        (Sum.inl SymbolMoveLabel.loop) (shiftLeftRoundTailProgram returnLabel right)
        (sparseShiftRightLocal_correct_nonempty
          (Nat.bodd word) (fixedBits w word.div2)) rfl state
        (shiftRoundBase (w + 1) word count fuel m base)
      rw [show Nat.bodd word :: fixedBits w word.div2 =
        fixedBits (w + 1) word by rfl] at hcore
      simp only [fixedBits_length] at hcore
      rw [shiftRight_core_bridge (R := R) (w + 1) word count fuel m base state
        hmove] at hcore
      let coreState := FullInterpreterState.shiftLens.put state default
      have hfirst := run_lensPhase_to_right
        (symbolMoveCoreRenaming .work6 .work0 (by decide))
        FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
        (Sum.inl SymbolMoveLabel.loop) (shiftRoundFinalProgram returnLabel right)
        (symbolMoveLocal_correct
          ((shiftRightBits (fixedBits (w + 1) word)).map SparseSymbol.bit) [])
        rfl coreState (shiftRightAfterCoreStacks (w + 1) word count fuel m base)
      have hshiftLength :
          (shiftRightBits (fixedBits (w + 1) word)).length = w + 1 := by
        rw [shiftRightBits_length_of_ne_nil (by
          intro hnil
          have hlen := congrArg List.length hnil
          simp at hlen)]
        simp
      simp only [hshiftLength,
        List.length_map, List.append_nil] at hfirst
      rw [shiftRight_firstMove_bridge (R := R) (w + 1) word count fuel m base
        coreState] at hfirst
      let firstState := FullInterpreterState.moveLens.put coreState default
      have hsecond := run_lensPhase_to_right
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
        returnLabel right
        (symbolMoveLocal_correct
          ((shiftRightBits (fixedBits (w + 1) word)).map SparseSymbol.bit).reverse [])
        rfl firstState
        (shiftRightAfterFirstMoveStacks (w + 1) word count fuel m base)
      simp only [List.length_reverse, List.length_map, hshiftLength,
        List.append_nil] at hsecond
      rw [shiftRight_return_bridge returnLabel (w + 1) word count fuel m base
        firstState hword] at hsecond
      have htail := chain_liftRightProgram
        (lensPhaseLeft
          (symbolMoveCoreRenaming .work6 .work0 (by decide))
          FullInterpreterState.moveLens symbolMoveCoreProgram .done
          (Sum.inl SymbolMoveLabel.loop))
        (shiftRoundFinalProgram returnLabel right) hfirst hsecond
      dsimp [coreState] at htail
      have hall := chain_liftRightProgram
        (lensPhaseLeft shiftRoundRenaming FullInterpreterState.shiftLens
          sparseShiftRightCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
        (shiftLeftRoundTailProgram returnLabel right) hcore htail
      refine ⟨FullInterpreterState.moveLens.put firstState default, ?_⟩
      simpa [shiftRightRoundProgram,
        show 4 * (w + 1) + 7 = (2 * (w + 1) + 3) +
          ((w + 1 + 2) + (w + 1 + 2)) by omega] using hall

end Lax51Proofs.RamToTM
