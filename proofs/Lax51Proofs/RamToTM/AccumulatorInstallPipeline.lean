import Lax51Proofs.RamToTM.PhaseComposition

namespace Lax51Proofs.RamToTM

open Turing TM2

abbrev AccInstallTailLabel (R : Type) := Sum SymbolMoveLabel R
abbrev AccInstallLabel (R : Type) := Sum SymbolMoveLabel (AccInstallTailLabel R)

def accInstallTailProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    AccInstallTailLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AccInstallTailLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def accInstallProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    AccInstallLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AccInstallLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (accInstallTailProgram returnLabel right)

def accInstallBase (old value : List Bool)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => old.map SparseSymbol.bit
  | .work0 => value.reverse.map SparseSymbol.bit
  | .work1 | .work2 | .work3 | .work4
  | .work5 | .work6 | .work7 => []
  | k => base k

def accInstallClearedBase (old value : List Bool)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .work0 => value.reverse.map SparseSymbol.bit
  | .work7 => old.reverse.map SparseSymbol.bit
  | .accumulator | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 => []
  | k => base k

theorem accInstall_clear_bridge {R : Type} (old value : List Bool)
    (base : CoreStack → List SparseSymbol) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      InterpreterMacroState.moveLens
      (Sum.inl SymbolMoveLabel.loop : AccInstallTailLabel R)
      (symbolMoveLocalCfg .done [] (old.reverse.map SparseSymbol.bit))
      default (accInstallBase old value base) =
    lensRenamedCfg (Λx := R)
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop
        (value.reverse.map SparseSymbol.bit) [])
      default (accInstallClearedBase old value base) := by
  simp [phaseReturnCfg, lensRenamedCfg, renamedStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, accInstallBase, accInstallClearedBase]
  funext k
  cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveStacks, accInstallBase,
    accInstallClearedBase]

def accInstallFinalCfg {R : Type} (returnLabel : R)
    (old value : List Bool) (base : CoreStack → List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (AccInstallLabel R) InterpreterMacroState :=
  mapLabelCfg (fun l : AccInstallTailLabel R => Sum.inr l)
    (mapLabelCfg (fun l : R => Sum.inr l)
      (phaseReturnCfg
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        InterpreterMacroState.moveLens returnLabel
        (symbolMoveLocalCfg .done [] (value.map SparseSymbol.bit))
        default (accInstallClearedBase old value base)))

theorem accInstall_correct {R : Type} (returnLabel : R)
    (rightProgram : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState)
    (old value : List Bool) (hlen : old.length = value.length)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step
      (accInstallProgram returnLabel rightProgram)))^[
        2 * old.length + 4])
      (some (lensRenamedCfg
        (symbolMoveCoreRenaming .accumulator .work7 (by decide))
        InterpreterMacroState.moveLens
        (symbolMoveLocalCfg .loop (old.map SparseSymbol.bit) [])
        default (accInstallBase old value base))) =
    some (accInstallFinalCfg returnLabel old value base) := by
  let clearMove := symbolMoveCoreRenaming .accumulator .work7 (by decide)
  let installMove := symbolMoveCoreRenaming .work0 .accumulator (by decide)
  have h₁ := run_lensPhase_to_right clearMove
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (accInstallTailProgram returnLabel rightProgram)
    (symbolMoveLocal_correct (old.map SparseSymbol.bit) []) rfl
    default (accInstallBase old value base)
  simp only [List.length_map, List.append_nil] at h₁
  rw [show (old.map SparseSymbol.bit).reverse =
      old.reverse.map SparseSymbol.bit by simp] at h₁
  rw [accInstall_clear_bridge (R := R) old value base] at h₁
  have h₂ := run_lensPhase_to_right installMove
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel rightProgram
    (symbolMoveLocal_correct (value.reverse.map SparseSymbol.bit) []) rfl
    default (accInstallClearedBase old value base)
  simp only [List.length_map, List.length_reverse, List.append_nil] at h₂
  simp only [List.map_reverse, List.reverse_reverse] at h₂
  have h₂' :
      ((fun o => o.bind (TM2.step
        (accInstallTailProgram returnLabel rightProgram)))^[
          value.length + 2])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens
          (symbolMoveLocalCfg .loop
            (value.reverse.map SparseSymbol.bit) [])
          default (accInstallClearedBase old value base))) =
      some (mapLabelCfg (fun l : R => Sum.inr l)
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens returnLabel
          (symbolMoveLocalCfg .done [] (value.map SparseSymbol.bit))
          default (accInstallClearedBase old value base))) := by
    simpa [accInstallTailProgram, installMove] using h₂
  have h := chain_liftRightProgram
    (lensPhaseLeft clearMove InterpreterMacroState.moveLens
      symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
    (accInstallTailProgram returnLabel rightProgram) h₁ h₂'
  have htime : 2 * old.length + 4 =
      (old.length + 2) + (value.length + 2) := by omega
  rw [htime]
  simpa [accInstallProgram, accInstallFinalCfg, clearMove] using h

theorem loadPipeline_fixed_correct {R : Type} (returnLabel : R)
    (rightProgram : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState)
    (w accumulator value : ℕ)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step
      (accInstallProgram returnLabel rightProgram)))^[2 * w + 4])
      (some (lensRenamedCfg
        (symbolMoveCoreRenaming .accumulator .work7 (by decide))
        InterpreterMacroState.moveLens
        (symbolMoveLocalCfg .loop
          ((fixedBits w accumulator).map SparseSymbol.bit) [])
        default
        (accInstallBase (fixedBits w accumulator) (fixedBits w value) base))) =
    some (accInstallFinalCfg returnLabel
      (fixedBits w accumulator) (fixedBits w value) base) := by
  simpa using accInstall_correct returnLabel rightProgram
    (fixedBits w accumulator) (fixedBits w value) (by simp) base

end Lax51Proofs.RamToTM
