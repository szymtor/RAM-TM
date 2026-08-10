import Lax51Proofs.RamToTM.AddInstruction
import Lax51Proofs.RamToTM.ZipPipeline

namespace Lax51Proofs.RamToTM

open Turing TM2

abbrev ClosedZipLabel := ZipPipelineLabel Unit

def closedZipProgram (f : Bool -> Bool -> Bool) : ClosedZipLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) ClosedZipLabel
      InterpreterMacroState :=
  zipPipelineProgram f () (fun _ => .halt)

def closedZipDone : ClosedZipLabel :=
  Sum.inr (Sum.inr (Sum.inr ()))

@[simp] theorem closedZipProgram_done (f : Bool -> Bool -> Bool) :
    closedZipProgram f closedZipDone = .halt := rfl

abbrev FullZipPhaseLabel (R : Type) := Sum ClosedZipLabel R

def fullZipPhaseProgram {N : Nat} {R : Type}
    (f : Bool -> Bool -> Bool) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullZipPhaseLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullZipPhaseLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming FullInterpreterState.macroLens
      (closedZipProgram f) closedZipDone returnLabel)
    right

def zipInitialLocal (f : Bool -> Bool -> Bool) (w a b : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      ClosedZipLabel InterpreterMacroState :=
  lensRenamedCfg (Λx := ZipTailLabel Unit)
    (symbolMoveCoreRenaming .work0 .work1 (by decide))
    InterpreterMacroState.moveLens
    (symbolMoveLocalCfg .loop
      ((fixedBits w b).reverse.map SparseSymbol.bit) [])
    default (zipPipelineBase (fixedBits w a)
      (operandBoundaryBase w a m base))

def zipFinalLocal (f : Bool -> Bool -> Bool) (w a b : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      ClosedZipLabel InterpreterMacroState :=
  mapLabelCfg (fun l : ZipTailLabel Unit => Sum.inr l)
    (mapLabelCfg (fun l : ZipFinishLabel Unit => Sum.inr l)
      (mapLabelCfg (fun l : Unit => Sum.inr l)
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens ()
          (symbolMoveLocalCfg .done []
            ((zipBits f (fixedBits w a) (fixedBits w b)).map
              SparseSymbol.bit))
          (zipAfterState (fixedBits w a) (fixedBits w b))
          (zipPipelineBase (fixedBits w a)
            (operandBoundaryBase w a m base)))))

theorem zipPhase_return_bridge {N : Nat} {R : Type}
    (f : Bool -> Bool -> Bool) (w a b result : Nat)
    (hresult : fixedBits w result =
      zipBits f (fixedBits w a) (fixedBits w b))
    (returnLabel : R) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (ambient : FullInterpreterState N)
    (ambientStacks : CoreStack -> List SparseSymbol) :
    phaseReturnCfg coreIdentityRenaming FullInterpreterState.macroLens
      returnLabel (zipFinalLocal f w a b m base) ambient ambientStacks =
    cleanReturnCfg returnLabel
      (FullInterpreterState.macroLens.put ambient
        (zipFinalLocal f w a b m base).var)
      (operandBoundaryBase w (result % 2 ^ w) m base) := by
  dsimp [zipFinalLocal]
  simp [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    coreIdentityRenaming, zipPipelineBase, operandBoundaryBase,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, renamedStacks, fixedBits_mod_word, ← hresult]
  funext k
  cases k <;> simp [zipPipelineBase, operandBoundaryBase,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, renamedStacks, fixedBits_mod_word, ← hresult]

theorem fullZipPhase_correct {N : Nat} {R : Type}
    (f : Bool -> Bool -> Bool) (w a b result : Nat)
    (hresult : fixedBits w result =
      zipBits f (fixedBits w a) (fixedBits w b))
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (ambient : FullInterpreterState N) :
    ∃ finalState,
      ((fun o => o.bind (TM2.step
        (fullZipPhaseProgram f returnLabel right)))^[3 * w + 7])
        (some (lensRenamedCfg coreIdentityRenaming
          FullInterpreterState.macroLens (zipInitialLocal f w a b m base)
          ambient (operandResultBase w a b m base))) =
      some (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel finalState
          (operandBoundaryBase w (result % 2 ^ w) m base))) := by
  have hsmall := zipPipeline_correct f () (fun _ => .halt)
    (fixedBits w a) (fixedBits w b) (by simp)
    (operandBoundaryBase w a m base)
  change _ = some (zipFinalLocal f w a b m base) at hsmall
  have h := run_lensPhase_to_right coreIdentityRenaming
    FullInterpreterState.macroLens (closedZipProgram f) closedZipDone
    (closedZipProgram_done f) returnLabel right hsmall rfl ambient
    (operandResultBase w a b m base)
  rw [zipPhase_return_bridge f w a b result hresult returnLabel m base
    ambient (operandResultBase w a b m base)] at h
  refine ⟨FullInterpreterState.macroLens.put ambient
    (zipFinalLocal f w a b m base).var, ?_⟩
  simpa [fullZipPhaseProgram, zipInitialLocal] using h

end Lax51Proofs.RamToTM
