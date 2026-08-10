import Lax51Proofs.RamToTM.PhaseComposition

namespace Lax51Proofs.RamToTM

open Turing TM2

private theorem iterate_two_more {X : Type} (f : X → X) (n : ℕ)
    {x y : X} (h : (f^[n]) (f (f x)) = y) :
    (f^[n + 2]) x = y := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    Function.iterate_succ_apply, Function.iterate_succ_apply]
  exact h

private theorem zipBits_length_of_eq (f : Bool → Bool → Bool)
    {left right : List Bool} (h : left.length = right.length) :
    (zipBits f left right).length = left.length := by
  induction left generalizing right with
  | nil => simp [zipBits]
  | cons a left ih =>
      cases right with
      | nil => simp at h
      | cons b right =>
          have htail : left.length = right.length := by simpa using h
          simp [zipBits, ih htail]

abbrev ZipFinishLabel (R : Type) := Sum SymbolMoveLabel R
abbrev ZipTailLabel (R : Type) := Sum AddLabel (ZipFinishLabel R)
abbrev ZipPipelineLabel (R : Type) := Sum SymbolMoveLabel (ZipTailLabel R)

def zipResultMoveProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    ZipFinishLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ZipFinishLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def zipTailProgram {R : Type} (f : Bool → Bool → Bool) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    ZipTailLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ZipTailLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft binaryCoreRenaming InterpreterMacroState.zipLens
      (sparseZipCoreProgram f) .done (Sum.inl .loop))
    (zipResultMoveProgram returnLabel right)

def zipPipelineProgram {R : Type} (f : Bool → Bool → Bool) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    ZipPipelineLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ZipPipelineLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done (Sum.inl .loop))
    (zipTailProgram f returnLabel right)

def zipPipelineBase (left : List Bool)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => left.map SparseSymbol.bit
  | .work0 | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem moveOperand_zip_bridge {R : Type} (f : Bool → Bool → Bool)
    (left rightBits : List Bool)
    (base : CoreStack → List SparseSymbol) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens
      (Sum.inl AddLabel.loop : ZipTailLabel R)
      (symbolMoveLocalCfg .done [] (rightBits.map SparseSymbol.bit))
      default (zipPipelineBase left base) =
    lensRenamedCfg (Λx := ZipFinishLabel R) binaryCoreRenaming
      InterpreterMacroState.zipLens
      (sparseZipLocalCfg f left rightBits []) default
      (zipPipelineBase left base) := by
  simp [phaseReturnCfg, lensRenamedCfg,
    zipPipelineBase, renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, binaryCoreRenaming, binaryCoreDecode,
    symbolMoveLocalCfg, sparseZipLocalCfg, symbolMoveStacks,
    mapAlphabetStacks, addStackFamily]
  constructor
  · rfl
  · funext k
    cases k <;> first | rfl | simp [renamedStacks, binaryCoreRenaming,
      binaryCoreDecode, symbolMoveCoreRenaming, symbolMoveCoreDecode,
      mapAlphabetStacks, addStackFamily, symbolMoveStacks, List.map_reverse,
      sparseBitEncode, Function.update]

def zipAfterState (left rightBits : List Bool) : InterpreterMacroState :=
  InterpreterMacroState.zipLens.put default
    ⟨none, none⟩

theorem zip_resultMove_bridge {R : Type} (f : Bool → Bool → Bool)
    (left rightBits : List Bool)
    (base : CoreStack → List SparseSymbol) :
    phaseReturnCfg binaryCoreRenaming InterpreterMacroState.zipLens
      (Sum.inl SymbolMoveLabel.loop : ZipFinishLabel R)
      (sparseZipLocalDoneCfg f (zipBits f left rightBits).reverse)
      default (zipPipelineBase left base) =
    lensRenamedCfg (Λx := R)
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop
        ((zipBits f left rightBits).reverse.map SparseSymbol.bit) [])
      (zipAfterState left rightBits) (zipPipelineBase left base) := by
  simp [phaseReturnCfg, lensRenamedCfg,
    zipAfterState, zipPipelineBase, renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, binaryCoreRenaming, binaryCoreDecode,
    symbolMoveLocalCfg, sparseZipLocalDoneCfg, symbolMoveStacks,
    mapAlphabetStacks, addStackFamily]
  constructor
  · rfl
  · funext k
    cases k <;> first | rfl | simp [renamedStacks, binaryCoreRenaming,
      binaryCoreDecode, symbolMoveCoreRenaming, symbolMoveCoreDecode,
      mapAlphabetStacks, addStackFamily, symbolMoveStacks, List.map_reverse,
      sparseBitEncode, Function.update]

theorem zipPipeline_correct {R : Type} (f : Bool → Bool → Bool)
    (returnLabel : R)
    (rightProgram : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState)
    (left rightBits : List Bool) (hlen : left.length = rightBits.length)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (zipPipelineProgram f returnLabel rightProgram)))^[
      3 * left.length + 6])
      (some (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        InterpreterMacroState.moveLens
        (symbolMoveLocalCfg .loop (rightBits.reverse.map SparseSymbol.bit) [])
        default (zipPipelineBase left base))) =
    some (mapLabelCfg (fun l : ZipTailLabel R => Sum.inr l)
      (mapLabelCfg (fun l : ZipFinishLabel R => Sum.inr l)
        (mapLabelCfg (fun l : R => Sum.inr l)
      (phaseReturnCfg
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        InterpreterMacroState.moveLens returnLabel
        (symbolMoveLocalCfg .done []
          ((zipBits f left rightBits).map SparseSymbol.bit))
        (zipAfterState left rightBits) (zipPipelineBase left base))))) := by
  let moveToOperand := symbolMoveCoreRenaming .work0 .work1 (by decide)
  let moveToAccumulator := symbolMoveCoreRenaming .work0 .accumulator (by decide)
  have h₁ := run_lensPhase_to_right moveToOperand
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl AddLabel.loop) (zipTailProgram f returnLabel rightProgram)
    (symbolMoveLocal_correct (rightBits.reverse.map SparseSymbol.bit) []) rfl
    default (zipPipelineBase left base)
  simp only [List.length_map, List.length_reverse] at h₁
  simp only [List.append_nil] at h₁
  dsimp [moveToOperand] at h₁
  rw [show (rightBits.reverse.map SparseSymbol.bit).reverse =
      rightBits.map SparseSymbol.bit by simp] at h₁
  rw [moveOperand_zip_bridge (R := R) f left rightBits base] at h₁
  have h₁' := iterate_two_more
    (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (ZipPipelineLabel R) InterpreterMacroState) =>
      o.bind (TM2.step (zipPipelineProgram f returnLabel rightProgram)))
    rightBits.length
    (x := some (lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop (rightBits.reverse.map SparseSymbol.bit) [])
      default (zipPipelineBase left base))) h₁
  have h₂ := run_lensPhase_to_right binaryCoreRenaming
    InterpreterMacroState.zipLens (sparseZipCoreProgram f) .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (zipResultMoveProgram returnLabel rightProgram)
    (sparseZipLocal_correct f left rightBits [] hlen) rfl
    default (zipPipelineBase left base)
  simp only [List.append_nil] at h₂
  rw [zip_resultMove_bridge (R := R) f left rightBits base] at h₂
  have h₃ := run_lensPhase_to_right moveToAccumulator
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel rightProgram
    (symbolMoveLocal_correct
      ((zipBits f left rightBits).reverse.map SparseSymbol.bit) []) rfl
    (zipAfterState left rightBits) (zipPipelineBase left base)
  simp only [List.length_map, List.length_reverse] at h₃
  simp only [List.append_nil] at h₃
  simp only [List.map_reverse, List.reverse_reverse] at h₃
  have h₃raw := h₃
  have h₃' :
      ((fun o => o.bind (TM2.step
        (zipResultMoveProgram returnLabel rightProgram)))^[
          (zipBits f left rightBits).length + 2])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens
          (symbolMoveLocalCfg .loop
            ((zipBits f left rightBits).reverse.map SparseSymbol.bit) [])
          (zipAfterState left rightBits) (zipPipelineBase left base))) =
        some (mapLabelCfg (fun l : R => Sum.inr l)
          (phaseReturnCfg
            (symbolMoveCoreRenaming .work0 .accumulator (by decide))
            InterpreterMacroState.moveLens returnLabel
            (symbolMoveLocalCfg .done []
              ((zipBits f left rightBits).map SparseSymbol.bit))
            (zipAfterState left rightBits) (zipPipelineBase left base))) := by
    simpa [zipResultMoveProgram, moveToAccumulator,
      List.map_reverse] using h₃raw
  have h₂₃ := chain_liftRightProgram
    (lensPhaseLeft binaryCoreRenaming InterpreterMacroState.zipLens
      (sparseZipCoreProgram f) .done (Sum.inl SymbolMoveLabel.loop))
    (zipResultMoveProgram returnLabel rightProgram) h₂ h₃'
  have h := chain_liftRightProgram
    (lensPhaseLeft moveToOperand InterpreterMacroState.moveLens
      symbolMoveCoreProgram .done (Sum.inl AddLabel.loop))
    (zipTailProgram f returnLabel rightProgram) h₁' h₂₃
  have hadd : (zipBits f left rightBits).length = left.length :=
    zipBits_length_of_eq f hlen
  rw [hadd] at h
  have htime : 3 * left.length + 6 =
      rightBits.length + 2 + (left.length + 1 + 1 + (left.length + 2)) := by
    omega
  rw [htime]
  simpa [zipPipelineProgram, moveToOperand] using h

end Lax51Proofs.RamToTM
