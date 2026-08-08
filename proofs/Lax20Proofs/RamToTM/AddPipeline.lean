import Lax20Proofs.RamToTM.PhaseComposition

namespace Lax20Proofs.RamToTM

open Turing TM2

private theorem iterate_two_more {X : Type} (f : X → X) (n : ℕ)
    {x y : X} (h : (f^[n]) (f (f x)) = y) :
    (f^[n + 2]) x = y := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    Function.iterate_succ_apply, Function.iterate_succ_apply]
  exact h

abbrev AddFinishLabel (R : Type) := Sum SymbolMoveLabel R
abbrev AddTailLabel (R : Type) := Sum AddLabel (AddFinishLabel R)
abbrev AddPipelineLabel (R : Type) := Sum SymbolMoveLabel (AddTailLabel R)

def addResultMoveProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    AddFinishLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AddFinishLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def addTailProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    AddTailLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AddTailLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft binaryCoreRenaming InterpreterMacroState.addLens
      sparseAddCoreProgram .done (Sum.inl .loop))
    (addResultMoveProgram returnLabel right)

def addPipelineProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    AddPipelineLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AddPipelineLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done (Sum.inl .loop))
    (addTailProgram returnLabel right)

def addPipelineBase (left : List Bool)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => left.map SparseSymbol.bit
  | .work0 | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem moveOperand_add_bridge {R : Type} (left rightBits : List Bool)
    (base : CoreStack → List SparseSymbol) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens
      (Sum.inl AddLabel.loop : AddTailLabel R)
      (symbolMoveLocalCfg .done [] (rightBits.map SparseSymbol.bit))
      default (addPipelineBase left base) =
    lensRenamedCfg (Λx := AddFinishLabel R) binaryCoreRenaming
      InterpreterMacroState.addLens
      (sparseAddLocalCfg false left rightBits []) default
      (addPipelineBase left base) := by
  simp [phaseReturnCfg, lensRenamedCfg,
    addPipelineBase, renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, binaryCoreRenaming, binaryCoreDecode,
    symbolMoveLocalCfg, sparseAddLocalCfg, symbolMoveStacks,
    mapAlphabetStacks, addStackFamily]
  constructor
  · rfl
  · funext k
    cases k <;> first | rfl | simp [renamedStacks, binaryCoreRenaming,
      binaryCoreDecode, symbolMoveCoreRenaming, symbolMoveCoreDecode,
      mapAlphabetStacks, addStackFamily, symbolMoveStacks, List.map_reverse,
      sparseBitEncode, Function.update]

def addAfterState (left rightBits : List Bool) : InterpreterMacroState :=
  InterpreterMacroState.addLens.put default
    ⟨addCarryOut left rightBits false, none, none⟩

theorem add_resultMove_bridge {R : Type} (left rightBits : List Bool)
    (base : CoreStack → List SparseSymbol) :
    phaseReturnCfg binaryCoreRenaming InterpreterMacroState.addLens
      (Sum.inl SymbolMoveLabel.loop : AddFinishLabel R)
      (sparseAddLocalDoneCfg (addCarryOut left rightBits false) []
        (addBits left rightBits false).reverse)
      default (addPipelineBase left base) =
    lensRenamedCfg (Λx := R)
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop
        ((addBits left rightBits false).reverse.map SparseSymbol.bit) [])
      (addAfterState left rightBits) (addPipelineBase left base) := by
  simp [phaseReturnCfg, lensRenamedCfg,
    addAfterState, addPipelineBase, renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, binaryCoreRenaming, binaryCoreDecode,
    symbolMoveLocalCfg, sparseAddLocalDoneCfg, symbolMoveStacks,
    mapAlphabetStacks, addStackFamily]
  constructor
  · rfl
  · funext k
    cases k <;> first | rfl | simp [renamedStacks, binaryCoreRenaming,
      binaryCoreDecode, symbolMoveCoreRenaming, symbolMoveCoreDecode,
      mapAlphabetStacks, addStackFamily, symbolMoveStacks, List.map_reverse,
      sparseBitEncode, Function.update]

theorem addPipeline_correct {R : Type} (returnLabel : R)
    (rightProgram : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState)
    (left rightBits : List Bool) (hlen : left.length = rightBits.length)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (addPipelineProgram returnLabel rightProgram)))^[
      3 * left.length + 6])
      (some (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        InterpreterMacroState.moveLens
        (symbolMoveLocalCfg .loop (rightBits.reverse.map SparseSymbol.bit) [])
        default (addPipelineBase left base))) =
    some (mapLabelCfg (fun l : AddTailLabel R => Sum.inr l)
      (mapLabelCfg (fun l : AddFinishLabel R => Sum.inr l)
        (mapLabelCfg (fun l : R => Sum.inr l)
      (phaseReturnCfg
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        InterpreterMacroState.moveLens returnLabel
        (symbolMoveLocalCfg .done []
          ((addBits left rightBits false).map SparseSymbol.bit))
        (addAfterState left rightBits) (addPipelineBase left base))))) := by
  let moveToOperand := symbolMoveCoreRenaming .work0 .work1 (by decide)
  let moveToAccumulator := symbolMoveCoreRenaming .work0 .accumulator (by decide)
  have h₁ := run_lensPhase_to_right moveToOperand
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl AddLabel.loop) (addTailProgram returnLabel rightProgram)
    (symbolMoveLocal_correct (rightBits.reverse.map SparseSymbol.bit) []) rfl
    default (addPipelineBase left base)
  simp only [List.length_map, List.length_reverse] at h₁
  simp only [List.append_nil] at h₁
  dsimp [moveToOperand] at h₁
  rw [show (rightBits.reverse.map SparseSymbol.bit).reverse =
      rightBits.map SparseSymbol.bit by simp] at h₁
  rw [moveOperand_add_bridge (R := R) left rightBits base] at h₁
  have h₁' := iterate_two_more
    (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (AddPipelineLabel R) InterpreterMacroState) =>
      o.bind (TM2.step (addPipelineProgram returnLabel rightProgram)))
    rightBits.length
    (x := some (lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop (rightBits.reverse.map SparseSymbol.bit) [])
      default (addPipelineBase left base))) h₁
  have h₂ := run_lensPhase_to_right binaryCoreRenaming
    InterpreterMacroState.addLens sparseAddCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (addResultMoveProgram returnLabel rightProgram)
    (sparseAddLocal_correct false left rightBits [] hlen) rfl
    default (addPipelineBase left base)
  simp only [List.append_nil] at h₂
  rw [add_resultMove_bridge (R := R) left rightBits base] at h₂
  have h₃ := run_lensPhase_to_right moveToAccumulator
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel rightProgram
    (symbolMoveLocal_correct
      ((addBits left rightBits false).reverse.map SparseSymbol.bit) []) rfl
    (addAfterState left rightBits) (addPipelineBase left base)
  simp only [List.length_map, List.length_reverse] at h₃
  simp only [List.append_nil] at h₃
  simp only [List.map_reverse, List.reverse_reverse] at h₃
  have h₃raw := h₃
  have h₃' :
      ((fun o => o.bind (TM2.step
        (addResultMoveProgram returnLabel rightProgram)))^[
          (addBits left rightBits false).length + 2])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens
          (symbolMoveLocalCfg .loop
            ((addBits left rightBits false).reverse.map SparseSymbol.bit) [])
          (addAfterState left rightBits) (addPipelineBase left base))) =
        some (mapLabelCfg (fun l : R => Sum.inr l)
          (phaseReturnCfg
            (symbolMoveCoreRenaming .work0 .accumulator (by decide))
            InterpreterMacroState.moveLens returnLabel
            (symbolMoveLocalCfg .done []
              ((addBits left rightBits false).map SparseSymbol.bit))
            (addAfterState left rightBits) (addPipelineBase left base))) := by
    simpa [addResultMoveProgram, moveToAccumulator,
      List.map_reverse] using h₃raw
  have h₂₃ := chain_liftRightProgram
    (lensPhaseLeft binaryCoreRenaming InterpreterMacroState.addLens
      sparseAddCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
    (addResultMoveProgram returnLabel rightProgram) h₂ h₃'
  have h := chain_liftRightProgram
    (lensPhaseLeft moveToOperand InterpreterMacroState.moveLens
      symbolMoveCoreProgram .done (Sum.inl AddLabel.loop))
    (addTailProgram returnLabel rightProgram) h₁' h₂₃
  have hadd : (addBits left rightBits false).length = left.length :=
    addBits_length_of_eq false hlen
  rw [hadd] at h
  have htime : 3 * left.length + 6 =
      rightBits.length + 2 + (left.length + 1 + 1 + (left.length + 2)) := by
    omega
  rw [htime]
  simpa [addPipelineProgram, moveToOperand] using h

end Lax20Proofs.RamToTM
