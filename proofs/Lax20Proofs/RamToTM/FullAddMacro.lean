import Lax20Proofs.RamToTM.StateProgramLift
import Lax20Proofs.RamToTM.AddPipeline

namespace Lax20Proofs.RamToTM

open Turing TM2

abbrev FullAddLabel := AddPipelineLabel Unit

def closedAddPipelineProgram : FullAddLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) FullAddLabel
      InterpreterMacroState :=
  addPipelineProgram () (fun _ => .halt)

def closedAddDone : FullAddLabel :=
  Sum.inr (Sum.inr (Sum.inr ()))

@[simp] theorem closedAddPipelineProgram_done :
    closedAddPipelineProgram closedAddDone = .halt := rfl

abbrev FullAddPhaseLabel (R : Type) := Sum FullAddLabel R

def fullAddPhaseProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullAddPhaseLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullAddPhaseLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming FullInterpreterState.macroLens
      closedAddPipelineProgram closedAddDone returnLabel)
    right

def fullAddMacroProgram {N : Nat} : FullAddLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) FullAddLabel
      (FullInterpreterState N) :=
  liftStateProgram FullInterpreterState.macroLens closedAddPipelineProgram

theorem fullAddMacro_correct {N : Nat}
    (left rightBits : List Bool) (hlen : left.length = rightBits.length)
    (base : CoreStack -> List SparseSymbol) (ambient : FullInterpreterState N) :
    ((fun o => o.bind (TM2.step fullAddMacroProgram))^[3 * left.length + 6])
      (some (liftStateCfg FullInterpreterState.macroLens
        (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .work1 (by decide))
          InterpreterMacroState.moveLens
          (symbolMoveLocalCfg .loop (rightBits.reverse.map SparseSymbol.bit) [])
          default (addPipelineBase left base)) ambient)) =
    some (liftStateCfg FullInterpreterState.macroLens
      (mapLabelCfg (fun l : AddTailLabel Unit => Sum.inr l)
        (mapLabelCfg (fun l : AddFinishLabel Unit => Sum.inr l)
          (mapLabelCfg (fun l : Unit => Sum.inr l)
            (phaseReturnCfg
              (symbolMoveCoreRenaming .work0 .accumulator (by decide))
              InterpreterMacroState.moveLens ()
              (symbolMoveLocalCfg .done []
                ((addBits left rightBits false).map SparseSymbol.bit))
              (addAfterState left rightBits) (addPipelineBase left base)))))
      ambient) := by
  apply transport_iterate_liftStateProgram
    FullInterpreterState.macroLens closedAddPipelineProgram
  exact addPipeline_correct () (fun _ => .halt) left rightBits hlen base

theorem fullAddMacro_fixed_correct {N : Nat}
    (w a b : Nat) (base : CoreStack -> List SparseSymbol)
    (ambient : FullInterpreterState N) :
    ((fun o => o.bind (TM2.step fullAddMacroProgram))^[3 * w + 6])
      (some (liftStateCfg FullInterpreterState.macroLens
        (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .work1 (by decide))
          InterpreterMacroState.moveLens
          (symbolMoveLocalCfg .loop
            ((fixedBits w b).reverse.map SparseSymbol.bit) [])
          default (addPipelineBase (fixedBits w a) base)) ambient)) =
    some (liftStateCfg FullInterpreterState.macroLens
      (mapLabelCfg (fun l : AddTailLabel Unit => Sum.inr l)
        (mapLabelCfg (fun l : AddFinishLabel Unit => Sum.inr l)
          (mapLabelCfg (fun l : Unit => Sum.inr l)
            (phaseReturnCfg
              (symbolMoveCoreRenaming .work0 .accumulator (by decide))
              InterpreterMacroState.moveLens ()
              (symbolMoveLocalCfg .done []
                ((addBits (fixedBits w a) (fixedBits w b) false).map
                  SparseSymbol.bit))
              (addAfterState (fixedBits w a) (fixedBits w b))
              (addPipelineBase (fixedBits w a) base))))) ambient) := by
  simpa using fullAddMacro_correct (N := N)
    (fixedBits w a) (fixedBits w b) (by simp) base ambient

def addInitialLocal (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      FullAddLabel InterpreterMacroState :=
  lensRenamedCfg (Λx := AddTailLabel Unit)
    (symbolMoveCoreRenaming .work0 .work1 (by decide))
    InterpreterMacroState.moveLens
    (symbolMoveLocalCfg .loop
      ((fixedBits w b).reverse.map SparseSymbol.bit) [])
    default (addPipelineBase (fixedBits w a)
      (operandBoundaryBase w a m base))

def addFinalLocal (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      FullAddLabel InterpreterMacroState :=
  mapLabelCfg (fun l : AddTailLabel Unit => Sum.inr l)
    (mapLabelCfg (fun l : AddFinishLabel Unit => Sum.inr l)
      (mapLabelCfg (fun l : Unit => Sum.inr l)
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens ()
          (symbolMoveLocalCfg .done []
            ((addBits (fixedBits w a) (fixedBits w b) false).map
              SparseSymbol.bit))
          (addAfterState (fixedBits w a) (fixedBits w b))
          (addPipelineBase (fixedBits w a)
            (operandBoundaryBase w a m base)))))

theorem addPhase_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (ambient : FullInterpreterState N)
    (ambientStacks : CoreStack -> List SparseSymbol) :
    phaseReturnCfg coreIdentityRenaming FullInterpreterState.macroLens
      returnLabel (addFinalLocal w a b m base) ambient ambientStacks =
    cleanReturnCfg returnLabel
      (FullInterpreterState.macroLens.put ambient
        (addFinalLocal w a b m base).var)
      (operandBoundaryBase w ((a + b) % 2 ^ w) m base) := by
  dsimp [addFinalLocal]
  simp [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    coreIdentityRenaming, renamedStacks_coreIdentity, addPipelineBase,
    operandBoundaryBase, symbolMoveCoreRenaming, symbolMoveCoreDecode,
    symbolMoveLocalCfg, symbolMoveStacks, renamedStacks, fixedBits_add,
    fixedBits_mod_word]
  funext k
  cases k <;> simp [addPipelineBase, operandBoundaryBase,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, renamedStacks, fixedBits_add, fixedBits_mod_word]

theorem fullAddPhase_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (ambient : FullInterpreterState N) :
    ∃ finalState,
      ((fun o => o.bind (TM2.step
        (fullAddPhaseProgram returnLabel right)))^[3 * w + 7])
        (some (lensRenamedCfg coreIdentityRenaming
          FullInterpreterState.macroLens (addInitialLocal w a b m base)
          ambient (operandResultBase w a b m base))) =
      some (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel finalState
          (operandBoundaryBase w ((a + b) % 2 ^ w) m base))) := by
  have hsmall := addPipeline_correct () (fun _ => .halt)
    (fixedBits w a) (fixedBits w b) (by simp)
    (operandBoundaryBase w a m base)
  change _ = some (addFinalLocal w a b m base) at hsmall
  have h := run_lensPhase_to_right coreIdentityRenaming
    FullInterpreterState.macroLens closedAddPipelineProgram closedAddDone
    closedAddPipelineProgram_done returnLabel right hsmall rfl ambient
    (operandResultBase w a b m base)
  rw [addPhase_return_bridge returnLabel w a b m base ambient
    (operandResultBase w a b m base)] at h
  let finalState := FullInterpreterState.macroLens.put ambient
    (addFinalLocal w a b m base).var
  refine ⟨finalState, ?_⟩
  simpa [fullAddPhaseProgram, addInitialLocal, finalState] using h

end Lax20Proofs.RamToTM
