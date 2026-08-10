import Lax51Proofs.RamToTM.ZipInstruction
import Lax51Proofs.RamToTM.MultiplyPipeline

namespace Lax51Proofs.RamToTM

open Turing TM2

abbrev ClosedMulLabel := MulPipelineLabel Unit

noncomputable local instance : DecidableEq ClosedMulLabel := Classical.decEq _

def closedMulProgram : ClosedMulLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) ClosedMulLabel
      InterpreterMacroState :=
  mulPipelineProgram () (fun _ => .halt)

def closedMulDone : ClosedMulLabel :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))

@[simp] theorem closedMulProgram_done :
    closedMulProgram closedMulDone = .halt := rfl

abbrev FullMulFinishLabel (R : Type) := Sum DiscardLabel R
abbrev FullMulLabel (R : Type) := Sum ClosedMulLabel (FullMulFinishLabel R)

def fullMulFinishProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work7)
      FullInterpreterState.moveLens discardProgram .done returnLabel)
    right

noncomputable def fullMulProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming FullInterpreterState.macroLens
      closedMulProgram closedMulDone (Sum.inl DiscardLabel.loop))
    (fullMulFinishProgram returnLabel right)

def mulInitialLocal (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) ClosedMulLabel
      InterpreterMacroState :=
  lensRenamedCfg (Λx := MulZeroLabel Unit)
    (symbolMoveCoreRenaming .work0 .work1 (by decide))
    InterpreterMacroState.moveLens
    (symbolMoveLocalCfg .loop
      ((fixedBits w b).reverse.map SparseSymbol.bit) [])
    default (mulPipelineBase w a (operandBoundaryBase w a m base))

def mulFinalLocal (w a b : Nat) (final : List Bool)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) ClosedMulLabel
      InterpreterMacroState :=
  mulPipelineFinalCfg () final (fixedBits w (a * b))
    (operandBoundaryBase w a m base)

theorem mul_discard_bridge {N : Nat} {R : Type}
    (w a b : Nat) (final : List Bool) (hfinal : final.length = w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (ambient : FullInterpreterState N)
    (ambientStacks : CoreStack -> List SparseSymbol) :
    phaseReturnCfg coreIdentityRenaming FullInterpreterState.macroLens
      (Sum.inl DiscardLabel.loop : FullMulFinishLabel R)
      (mulFinalLocal w a b final m base) ambient ambientStacks =
    lensRenamedCfg (discardCoreRenaming .work7)
      FullInterpreterState.moveLens
      (discardCfg .loop (final.reverse.map SparseSymbol.bit))
      (FullInterpreterState.macroLens.put ambient
        (mulFinalLocal w a b final m base).var)
      (operandBoundaryBase w ((a * b) % 2 ^ w) m base) := by
  dsimp [mulFinalLocal, mulPipelineFinalCfg]
  simp [phaseReturnCfg, lensRenamedCfg, coreIdentityRenaming,
    discardCoreRenaming, discardCfg, discardStacks, mulClearedBase,
    operandBoundaryBase, symbolMoveCoreRenaming, symbolMoveCoreDecode,
    symbolMoveLocalCfg, symbolMoveStacks, renamedStacks,
    fixedBits_mod_word]
  constructor
  · rfl
  · funext k
    cases k <;> simp [mulClearedBase, operandBoundaryBase,
      discardCoreRenaming, discardCfg, discardStacks,
      symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
      symbolMoveStacks, renamedStacks, fixedBits_mod_word, hfinal]
      <;> rfl

theorem fullMul_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b : Nat) (hw : 0 < w) (hb : b < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (ambient : FullInterpreterState N) :
    ∃ finalState,
      ((fun o => o.bind (TM2.step (fullMulProgram returnLabel right)))^[
        mulRunTime (fixedBits w b) w + 7 * w + 15])
        (some (lensRenamedCfg coreIdentityRenaming
          FullInterpreterState.macroLens (mulInitialLocal w a b m base)
          ambient (operandResultBase w a b m base))) =
      some (mapLabelCfg (fun l : FullMulFinishLabel R => Sum.inr l)
        (mapLabelCfg (fun l : R => Sum.inr l)
          (cleanReturnCfg returnLabel finalState
            (operandBoundaryBase w ((a * b) % 2 ^ w) m base)))) := by
  rcases mulPipeline_correct () (fun _ => .halt) w a b hw hb
      (operandBoundaryBase w a m base) with ⟨final, hfinal, hsmall⟩
  change _ = some (mulFinalLocal w a b final m base) at hsmall
  have hmul := run_lensPhase_to_right coreIdentityRenaming
    FullInterpreterState.macroLens closedMulProgram closedMulDone
    closedMulProgram_done (Sum.inl DiscardLabel.loop)
    (fullMulFinishProgram returnLabel right) hsmall rfl ambient
    (operandResultBase w a b m base)
  rw [mul_discard_bridge (R := R) w a b final hfinal m base ambient
    (operandResultBase w a b m base)] at hmul
  let stateAfterMul := FullInterpreterState.macroLens.put ambient
    (mulFinalLocal w a b final m base).var
  have hdiscard := run_lensPhase_to_right (discardCoreRenaming .work7)
    FullInterpreterState.moveLens discardProgram .done (by rfl)
    returnLabel right
    (discard_correct (final.reverse.map SparseSymbol.bit)) rfl
    stateAfterMul (operandBoundaryBase w ((a * b) % 2 ^ w) m base)
  simp only [List.length_map, List.length_reverse, hfinal] at hdiscard
  rw [discard_loadReturn_bridge returnLabel w a
    ((a * b) % 2 ^ w) m base stateAfterMul] at hdiscard
  have hchain := chain_liftRightProgram
    (lensPhaseLeft coreIdentityRenaming FullInterpreterState.macroLens
      closedMulProgram closedMulDone (Sum.inl DiscardLabel.loop))
    (fullMulFinishProgram returnLabel right) hmul hdiscard
  refine ⟨FullInterpreterState.moveLens.put stateAfterMul default, ?_⟩
  have htime : mulRunTime (fixedBits w b) w + 7 * w + 15 =
      (mulRunTime (fixedBits w b) w + 6 * w + 12 + 1) +
        (w + 1 + 1) := by omega
  rw [htime]
  simpa [fullMulProgram, mulInitialLocal, stateAfterMul] using hchain

end Lax51Proofs.RamToTM
