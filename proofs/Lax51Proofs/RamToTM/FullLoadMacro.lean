import Lax51Proofs.RamToTM.OperandEvaluator
import Lax51Proofs.RamToTM.AccumulatorInstallPipeline

namespace Lax51Proofs.RamToTM

open Turing TM2

abbrev ClosedAccInstallLabel := AccInstallLabel Unit

def closedAccInstallProgram : ClosedAccInstallLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) ClosedAccInstallLabel
      InterpreterMacroState :=
  accInstallProgram () (fun _ => .halt)

def closedAccInstallDone : ClosedAccInstallLabel :=
  Sum.inr (Sum.inr ())

@[simp] theorem closedAccInstallProgram_done :
    closedAccInstallProgram closedAccInstallDone = .halt := rfl

abbrev FullLoadFinishLabel (R : Type) := Sum DiscardLabel R
abbrev FullLoadLabel (R : Type) :=
  Sum ClosedAccInstallLabel (FullLoadFinishLabel R)

def fullLoadFinishProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullLoadFinishLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullLoadFinishLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work7)
      FullInterpreterState.moveLens discardProgram .done returnLabel)
    right

def fullLoadProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullLoadLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullLoadLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming FullInterpreterState.macroLens
      closedAccInstallProgram closedAccInstallDone
      (Sum.inl DiscardLabel.loop))
    (fullLoadFinishProgram returnLabel right)

def embedClosedAccFinal {N : Nat} {R : Type}
    (c : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      ClosedAccInstallLabel InterpreterMacroState)
    (ambient : FullInterpreterState N) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (FullLoadLabel R) (FullInterpreterState N) :=
  lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens c
    ambient c.stk

theorem accInstall_discard_bridge {N : Nat} {R : Type}
    (w old value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (ambient : FullInterpreterState N)
    (ambientStacks : CoreStack -> List SparseSymbol) :
    phaseReturnCfg coreIdentityRenaming FullInterpreterState.macroLens
      (Sum.inl DiscardLabel.loop : FullLoadFinishLabel R)
      (accInstallFinalCfg () (fixedBits w old) (fixedBits w value)
        (operandBoundaryBase w old m base))
      ambient ambientStacks =
    lensRenamedCfg (discardCoreRenaming .work7)
        FullInterpreterState.moveLens
        (discardCfg .loop
          ((fixedBits w old).reverse.map SparseSymbol.bit))
        (FullInterpreterState.macroLens.put ambient
          (accInstallFinalCfg () (fixedBits w old) (fixedBits w value)
            (operandBoundaryBase w old m base)).var)
        (operandBoundaryBase w value m base) := by
  dsimp [accInstallFinalCfg]
  simp [phaseReturnCfg, accInstallFinalCfg, lensRenamedCfg,
    coreIdentityRenaming, renamedStacks_coreIdentity,
    discardCoreRenaming, discardCfg, discardStacks,
    accInstallClearedBase, operandBoundaryBase,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, renamedStacks, List.map_reverse]
  constructor
  · rfl
  · funext k
    cases k <;> simp [accInstallFinalCfg, accInstallClearedBase,
      operandBoundaryBase, symbolMoveCoreRenaming, symbolMoveCoreDecode,
      symbolMoveLocalCfg, symbolMoveStacks, renamedStacks, List.map_reverse]
      <;> rfl

theorem discard_loadReturn_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w old value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg (discardCoreRenaming .work7)
      FullInterpreterState.moveLens returnLabel
      (discardCfg .done []) state (operandBoundaryBase w value m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (operandBoundaryBase w value m base) := by
  simp [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    discardCoreRenaming, discardCfg, discardStacks, renamedStacks,
    operandBoundaryBase]
  funext k
  cases k <;> rfl

theorem fullLoadMacro_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w old value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (ambient : FullInterpreterState N) :
    let initialLocal := lensRenamedCfg (Λx := AccInstallTailLabel Unit)
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop
        ((fixedBits w old).map SparseSymbol.bit) [])
      default
      (accInstallBase (fixedBits w old) (fixedBits w value)
        (operandBoundaryBase w old m base))
    ∃ finalState,
      ((fun o => o.bind (TM2.step
        (fullLoadProgram returnLabel right)))^[3 * w + 7])
        (some (lensRenamedCfg coreIdentityRenaming
          FullInterpreterState.macroLens initialLocal ambient
          (operandResultBase w old value m base))) =
      some (mapLabelCfg (fun l : FullLoadFinishLabel R => Sum.inr l)
        (mapLabelCfg (fun l : R => Sum.inr l)
          (cleanReturnCfg returnLabel finalState
            (operandBoundaryBase w value m base)))) := by
  dsimp only
  let initialLocal := lensRenamedCfg (Λx := AccInstallTailLabel Unit)
    (symbolMoveCoreRenaming .accumulator .work7 (by decide))
    InterpreterMacroState.moveLens
    (symbolMoveLocalCfg .loop
      ((fixedBits w old).map SparseSymbol.bit) [])
    default
    (accInstallBase (fixedBits w old) (fixedBits w value)
      (operandBoundaryBase w old m base))
  have hsmall := loadPipeline_fixed_correct () (fun _ => .halt)
    w old value (operandBoundaryBase w old m base)
  have hacc := run_lensPhase_to_right coreIdentityRenaming
    FullInterpreterState.macroLens closedAccInstallProgram
    closedAccInstallDone closedAccInstallProgram_done
    (Sum.inl DiscardLabel.loop) (fullLoadFinishProgram returnLabel right)
    hsmall rfl ambient (operandResultBase w old value m base)
  rw [accInstall_discard_bridge (R := R) w old value m base ambient
    (operandResultBase w old value m base)] at hacc
  let stateAfterAcc := FullInterpreterState.macroLens.put ambient
    (accInstallFinalCfg () (fixedBits w old) (fixedBits w value)
      (operandBoundaryBase w old m base)).var
  have hdiscard := run_lensPhase_to_right
    (discardCoreRenaming .work7) FullInterpreterState.moveLens
    discardProgram .done (by rfl) returnLabel right
    (discard_correct
      ((fixedBits w old).reverse.map SparseSymbol.bit)) rfl
    stateAfterAcc (operandBoundaryBase w value m base)
  simp only [List.length_map, List.length_reverse, fixedBits_length] at hdiscard
  rw [discard_loadReturn_bridge returnLabel w old value m base stateAfterAcc]
    at hdiscard
  have hchain := chain_liftRightProgram
    (lensPhaseLeft coreIdentityRenaming FullInterpreterState.macroLens
      closedAccInstallProgram closedAccInstallDone
      (Sum.inl DiscardLabel.loop))
    (fullLoadFinishProgram returnLabel right) hacc hdiscard
  refine ⟨FullInterpreterState.moveLens.put stateAfterAcc default, ?_⟩
  have htime : 3 * w + 7 = (2 * w + 4 + 1) + (w + 1 + 1) := by omega
  rw [htime]
  simpa [fullLoadProgram, initialLocal, stateAfterAcc] using hchain

end Lax51Proofs.RamToTM
