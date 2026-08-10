import Lax51Proofs.RamToTM.PhaseComposition

namespace Lax51Proofs.RamToTM

open Turing TM2

abbrev MulInstallLabel (R : Type) := Sum SymbolMoveLabel R
abbrev MulClearLabel (R : Type) := Sum SymbolMoveLabel (MulInstallLabel R)
abbrev MulReverseLabel (R : Type) := Sum SymbolMoveLabel (MulClearLabel R)
abbrev MulArithmeticLabel (R : Type) := Sum MulLabel (MulReverseLabel R)
abbrev MulZeroLabel (R : Type) := Sum ZeroWordLabel (MulArithmeticLabel R)
abbrev MulPipelineLabel (R : Type) := Sum SymbolMoveLabel (MulZeroLabel R)

def mulInstallProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulInstallLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulInstallLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work2 .accumulator (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def mulClearProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulClearLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulClearLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (mulInstallProgram returnLabel right)

def mulReverseProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulReverseLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulReverseLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (mulClearProgram returnLabel right)

def mulArithmeticProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulArithmeticLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulArithmeticLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft mulCoreRenaming InterpreterMacroState.mulLens
      sparseMulCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
    (mulReverseProgram returnLabel right)

def mulZeroProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulZeroLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulZeroLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft zeroWordCoreRenaming InterpreterMacroState.zeroLens
      zeroWordProgram .done (Sum.inl MulLabel.outer))
    (mulArithmeticProgram returnLabel right)

def mulPipelineProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulPipelineLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulPipelineLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (mulZeroProgram returnLabel right)

def mulPipelineBase (w a : ℕ)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => (fixedBits w a).map SparseSymbol.bit
  | .work0 | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def mulOperandBase (w a b : ℕ)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => (fixedBits w a).map SparseSymbol.bit
  | .work1 => (fixedBits w b).map SparseSymbol.bit
  | .work0 | .work2 | .work3 | .work4
  | .work5 | .work6 | .work7 => []
  | k => base k

theorem mul_operand_zero_bridge {R : Type} (w a b : ℕ)
    (base : CoreStack → List SparseSymbol) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens
      (Sum.inl ZeroWordLabel.fill : MulZeroLabel R)
      (symbolMoveLocalCfg .done [] ((fixedBits w b).map SparseSymbol.bit))
      default (mulPipelineBase w a base) =
    lensRenamedCfg (Λx := MulArithmeticLabel R) zeroWordCoreRenaming
      InterpreterMacroState.zeroLens
      (zeroWordTypedCfg .fill
        ((fixedBits w a).map SparseSymbol.bit) [] [])
      default (mulOperandBase w a b base) := by
  simp [phaseReturnCfg, lensRenamedCfg, mulPipelineBase, renamedStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, zeroWordCoreRenaming,
    zeroWordCoreDecode, symbolMoveLocalCfg, zeroWordTypedCfg,
      symbolMoveStacks, zeroWordStacks, mulOperandBase]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
      symbolMoveCoreDecode, zeroWordCoreRenaming, zeroWordCoreDecode,
      symbolMoveStacks, zeroWordStacks, mulPipelineBase, mulOperandBase]

theorem mul_zero_arithmetic_bridge {R : Type} (w a b : ℕ)
    (base : CoreStack → List SparseSymbol) :
    phaseReturnCfg zeroWordCoreRenaming InterpreterMacroState.zeroLens
      (Sum.inl MulLabel.outer : MulArithmeticLabel R)
      (zeroWordTypedCfg .done
        ((fixedBits w a).map SparseSymbol.bit) []
        (List.replicate w (.bit false)))
      default (mulOperandBase w a b base) =
    lensRenamedCfg (Λx := MulReverseLabel R) mulCoreRenaming
      InterpreterMacroState.mulLens
      (sparseMulLocalOuterCfg
        (fixedBits w b) (fixedBits w a) (fixedBits w 0))
      default (mulOperandBase w a b base) := by
  simp [phaseReturnCfg, lensRenamedCfg, mulPipelineBase, renamedStacks,
    zeroWordCoreRenaming, zeroWordCoreDecode, mulCoreRenaming, mulCoreDecode,
    zeroWordTypedCfg, zeroWordStacks, sparseMulLocalOuterCfg,
    mapAlphabetStacks, mulStacks, fixedBits_zero, List.map_replicate,
    mulOperandBase]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks, zeroWordCoreRenaming,
      zeroWordCoreDecode, mulCoreRenaming, mulCoreDecode, zeroWordStacks,
      mapAlphabetStacks, mulStacks, mulPipelineBase, mulOperandBase,
      sparseBitEncode,
      fixedBits_zero, List.map_replicate]

def mulProductBase (final product : List Bool)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => final.map SparseSymbol.bit
  | .work0 => product.map SparseSymbol.bit
  | .work1 | .work2 | .work3 | .work4
  | .work5 | .work6 | .work7 => []
  | k => base k

theorem mul_arithmetic_reverse_bridge {R : Type}
    (w a b : ℕ) (final product : List Bool)
    (base : CoreStack → List SparseSymbol) :
    phaseReturnCfg mulCoreRenaming InterpreterMacroState.mulLens
      (Sum.inl SymbolMoveLabel.loop : MulReverseLabel R)
      (sparseMulLocalDoneCfg final product)
      default (mulOperandBase w a b base) =
    lensRenamedCfg (Λx := MulClearLabel R)
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop (product.map SparseSymbol.bit) [])
      default (mulProductBase final product base) := by
  simp [phaseReturnCfg, lensRenamedCfg, renamedStacks, mulCoreRenaming,
    mulCoreDecode, sparseMulLocalDoneCfg, mapAlphabetStacks, mulStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, mulOperandBase, mulProductBase, sparseBitEncode]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks, mulCoreRenaming, mulCoreDecode,
      mapAlphabetStacks, mulStacks, symbolMoveCoreRenaming,
      symbolMoveCoreDecode, symbolMoveStacks, mulOperandBase,
      mulProductBase, sparseBitEncode]

def mulReversedBase (final product : List Bool)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => final.map SparseSymbol.bit
  | .work2 => product.reverse.map SparseSymbol.bit
  | .work0 | .work1 | .work3 | .work4
  | .work5 | .work6 | .work7 => []
  | k => base k

theorem mul_reverse_clear_bridge {R : Type}
    (final product : List Bool) (base : CoreStack → List SparseSymbol) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      InterpreterMacroState.moveLens
      (Sum.inl SymbolMoveLabel.loop : MulClearLabel R)
      (symbolMoveLocalCfg .done []
        (product.reverse.map SparseSymbol.bit))
      default (mulProductBase final product base) =
    lensRenamedCfg (Λx := MulInstallLabel R)
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop (final.map SparseSymbol.bit) [])
      default (mulReversedBase final product base) := by
  simp [phaseReturnCfg, lensRenamedCfg, renamedStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, mulProductBase, mulReversedBase]
  funext k
  cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveStacks, mulProductBase,
    mulReversedBase]

def mulClearedBase (final product : List Bool)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .work2 => product.reverse.map SparseSymbol.bit
  | .work7 => final.reverse.map SparseSymbol.bit
  | .accumulator | .work0 | .work1 | .work3
  | .work4 | .work5 | .work6 => []
  | k => base k

theorem mul_clear_install_bridge {R : Type}
    (final product : List Bool) (base : CoreStack → List SparseSymbol) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      InterpreterMacroState.moveLens
      (Sum.inl SymbolMoveLabel.loop : MulInstallLabel R)
      (symbolMoveLocalCfg .done []
        (final.reverse.map SparseSymbol.bit))
      default (mulReversedBase final product base) =
    lensRenamedCfg (Λx := R)
      (symbolMoveCoreRenaming .work2 .accumulator (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop
        (product.reverse.map SparseSymbol.bit) [])
      default (mulClearedBase final product base) := by
  simp [phaseReturnCfg, lensRenamedCfg, renamedStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, mulReversedBase, mulClearedBase]
  funext k
  cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveStacks, mulReversedBase,
    mulClearedBase]

def mulPipelineFinalCfg {R : Type} (returnLabel : R)
    (final product : List Bool) (base : CoreStack → List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (MulPipelineLabel R) InterpreterMacroState :=
  mapLabelCfg (fun l : MulZeroLabel R => Sum.inr l)
    (mapLabelCfg (fun l : MulArithmeticLabel R => Sum.inr l)
      (mapLabelCfg (fun l : MulReverseLabel R => Sum.inr l)
        (mapLabelCfg (fun l : MulClearLabel R => Sum.inr l)
          (mapLabelCfg (fun l : MulInstallLabel R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (phaseReturnCfg
                (symbolMoveCoreRenaming .work2 .accumulator (by decide))
                InterpreterMacroState.moveLens returnLabel
                (symbolMoveLocalCfg .done [] (product.map SparseSymbol.bit))
                default (mulClearedBase final product base)))))))

theorem mulPipeline_correct {R : Type} (returnLabel : R)
    (rightProgram : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState)
    (w a b : ℕ) (hw : 0 < w) (hb : b < 2 ^ w)
    (base : CoreStack → List SparseSymbol) :
    ∃ finalMultiplicand : List Bool, finalMultiplicand.length = w ∧
      ((fun o => o.bind (TM2.step
        (mulPipelineProgram returnLabel rightProgram)))^[
          mulRunTime (fixedBits w b) w + 6 * w + 12])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .work1 (by decide))
          InterpreterMacroState.moveLens
          (symbolMoveLocalCfg .loop
            ((fixedBits w b).reverse.map SparseSymbol.bit) [])
          default (mulPipelineBase w a base))) =
      some (mulPipelineFinalCfg returnLabel finalMultiplicand
        (fixedBits w (a * b)) base) := by
  let operandMove := symbolMoveCoreRenaming .work0 .work1 (by decide)
  let reverseMove := symbolMoveCoreRenaming .work0 .work2 (by decide)
  let clearMove := symbolMoveCoreRenaming .accumulator .work7 (by decide)
  let installMove := symbolMoveCoreRenaming .work2 .accumulator (by decide)
  have h₁ := run_lensPhase_to_right operandMove
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl ZeroWordLabel.fill) (mulZeroProgram returnLabel rightProgram)
    (symbolMoveLocal_correct
      ((fixedBits w b).reverse.map SparseSymbol.bit) []) rfl
    default (mulPipelineBase w a base)
  simp only [List.length_map, List.length_reverse, fixedBits_length,
    List.append_nil] at h₁
  rw [show ((fixedBits w b).reverse.map SparseSymbol.bit).reverse =
      (fixedBits w b).map SparseSymbol.bit by simp] at h₁
  rw [mul_operand_zero_bridge (R := R) w a b base] at h₁
  have h₂ := run_lensPhase_to_right zeroWordCoreRenaming
    InterpreterMacroState.zeroLens zeroWordProgram .done (by rfl)
    (Sum.inl MulLabel.outer) (mulArithmeticProgram returnLabel rightProgram)
    (zeroWordTyped_correct ((fixedBits w a).map SparseSymbol.bit) []) rfl
    default (mulOperandBase w a b base)
  simp only [List.length_map, fixedBits_length, List.append_nil] at h₂
  rw [mul_zero_arithmetic_bridge (R := R) w a b base] at h₂
  rcases sparseMulLocal_fixed_correct_with_length w a b hw hb with
    ⟨final, hfinal, hmul⟩
  have h₃ := run_lensPhase_to_right mulCoreRenaming
    InterpreterMacroState.mulLens sparseMulCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (mulReverseProgram returnLabel rightProgram)
    hmul rfl default (mulOperandBase w a b base)
  rw [mul_arithmetic_reverse_bridge (R := R) w a b final
    (fixedBits w (a * b)) base] at h₃
  have h₄ := run_lensPhase_to_right reverseMove
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (mulClearProgram returnLabel rightProgram)
    (symbolMoveLocal_correct
      ((fixedBits w (a * b)).map SparseSymbol.bit) []) rfl
    default (mulProductBase final (fixedBits w (a * b)) base)
  simp only [List.length_map, fixedBits_length, List.append_nil] at h₄
  rw [show ((fixedBits w (a * b)).map SparseSymbol.bit).reverse =
      (fixedBits w (a * b)).reverse.map SparseSymbol.bit by simp] at h₄
  rw [mul_reverse_clear_bridge (R := R) final
    (fixedBits w (a * b)) base] at h₄
  have h₅ := run_lensPhase_to_right clearMove
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (mulInstallProgram returnLabel rightProgram)
    (symbolMoveLocal_correct (final.map SparseSymbol.bit) []) rfl
    default (mulReversedBase final (fixedBits w (a * b)) base)
  simp only [List.length_map, List.append_nil, hfinal] at h₅
  rw [show (final.map SparseSymbol.bit).reverse =
      final.reverse.map SparseSymbol.bit by simp] at h₅
  rw [mul_clear_install_bridge (R := R) final
    (fixedBits w (a * b)) base] at h₅
  have h₆ := run_lensPhase_to_right installMove
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel rightProgram
    (symbolMoveLocal_correct
      ((fixedBits w (a * b)).reverse.map SparseSymbol.bit) []) rfl
    default (mulClearedBase final (fixedBits w (a * b)) base)
  simp only [List.length_map, List.length_reverse, fixedBits_length,
    List.append_nil] at h₆
  simp only [List.map_reverse, List.reverse_reverse] at h₆
  have h₆' :
      ((fun o => o.bind (TM2.step
        (mulInstallProgram returnLabel rightProgram)))^[w + 2])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work2 .accumulator (by decide))
          InterpreterMacroState.moveLens
          (symbolMoveLocalCfg .loop
            ((fixedBits w (a * b)).reverse.map SparseSymbol.bit) [])
          default (mulClearedBase final (fixedBits w (a * b)) base))) =
      some (mapLabelCfg (fun l : R => Sum.inr l)
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work2 .accumulator (by decide))
          InterpreterMacroState.moveLens returnLabel
          (symbolMoveLocalCfg .done []
            ((fixedBits w (a * b)).map SparseSymbol.bit))
          default (mulClearedBase final (fixedBits w (a * b)) base))) := by
    simpa [mulInstallProgram, installMove] using h₆
  have h₅₆ := chain_liftRightProgram
    (lensPhaseLeft clearMove InterpreterMacroState.moveLens
      symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
    (mulInstallProgram returnLabel rightProgram) h₅ h₆'
  have h₄₆ := chain_liftRightProgram
    (lensPhaseLeft reverseMove InterpreterMacroState.moveLens
      symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
    (mulClearProgram returnLabel rightProgram) h₄ h₅₆
  have h₃₆ := chain_liftRightProgram
    (lensPhaseLeft mulCoreRenaming InterpreterMacroState.mulLens
      sparseMulCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
    (mulReverseProgram returnLabel rightProgram) h₃ h₄₆
  have h₂₆ := chain_liftRightProgram
    (lensPhaseLeft zeroWordCoreRenaming InterpreterMacroState.zeroLens
      zeroWordProgram .done (Sum.inl MulLabel.outer))
    (mulArithmeticProgram returnLabel rightProgram) h₂ h₃₆
  have h := chain_liftRightProgram
    (lensPhaseLeft operandMove InterpreterMacroState.moveLens
      symbolMoveCoreProgram .done (Sum.inl ZeroWordLabel.fill))
    (mulZeroProgram returnLabel rightProgram) h₁ h₂₆
  refine ⟨final, hfinal, ?_⟩
  have htime :
      mulRunTime (fixedBits w b) w + 6 * w + 12 =
        (w + 2) + (2 * w + 2 + 1 +
          (mulRunTime (fixedBits w b) w + 1 +
            (w + 2 + (w + 2 + (w + 2))))) := by
    omega
  rw [htime]
  simpa [mulPipelineProgram, mulPipelineFinalCfg, operandMove,
    reverseMove, clearMove, installMove] using h

end Lax51Proofs.RamToTM
