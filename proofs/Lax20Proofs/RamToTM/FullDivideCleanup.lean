import Lax20Proofs.RamToTM.FullDivideCore

namespace Lax20Proofs.RamToTM

open Turing TM2

abbrev DivideCleanupFinalLabel (R : Type) := Sum DiscardLabel R
abbrev DivideCleanupTailLabel (R : Type) :=
  Sum DiscardLabel (DivideCleanupFinalLabel R)
abbrev FullDivideCleanLabel (R : Type) := Sum DivLabel (DivideCleanupTailLabel R)

def divideCleanupFinalProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideCleanupFinalLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideCleanupFinalLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work2)
      FullInterpreterState.moveLens discardProgram .done returnLabel)
    right

def divideCleanupTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideCleanupTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideCleanupTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl DiscardLabel.loop))
    (divideCleanupFinalProgram returnLabel right)

def fullDivideCleanProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullDivideCleanLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullDivideCleanLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft preparedDivRenaming FullInterpreterState.divLens
      sparseDivCoreProgram .done (Sum.inl DiscardLabel.loop))
    (divideCleanupTailProgram returnLabel right)

def divideAfterFirstCleanupStacks (w remainder quotient : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w quotient).map SparseSymbol.bit
  | .work2 => (fixedBits (w + 1) remainder).map SparseSymbol.bit
  | .work0 | .work1 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | k => base k

theorem divideFirstCleanup_bridge {N : Nat} {R : Type}
    (w d remainder quotient : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    cleanReturnCfg (Sum.inl DiscardLabel.loop : DivideCleanupTailLabel R)
      state (divideCoreResultStacks w d remainder quotient m base) =
    lensRenamedCfg (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (discardCfg .loop ((fixedBits (w + 1) d).map SparseSymbol.bit))
      state (divideCoreResultStacks w d remainder quotient m base) := by
  simp [cleanReturnCfg, lensRenamedCfg, discardCoreRenaming, discardCfg,
    discardStacks, divideCoreResultStacks, renamedStacks]
  constructor
  · symm
    rw [← hmove, FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [renamedStacks, discardCoreRenaming, discardCfg,
      discardStacks, divideCoreResultStacks]

theorem divideSecondCleanup_bridge {N : Nat} {R : Type}
    (w remainder quotient : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (Sum.inl DiscardLabel.loop : DivideCleanupFinalLabel R)
      (discardCfg .done []) state
      (divideCoreResultStacks w 0 remainder quotient m base) =
    lensRenamedCfg (discardCoreRenaming .work2)
      FullInterpreterState.moveLens
      (discardCfg .loop
        ((fixedBits (w + 1) remainder).map SparseSymbol.bit))
      (FullInterpreterState.moveLens.put state default)
      (divideAfterFirstCleanupStacks w remainder quotient m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, discardCoreRenaming, discardCfg,
    discardStacks, divideCoreResultStacks, divideAfterFirstCleanupStacks,
    renamedStacks]
  constructor
  · rfl
  · funext k
    cases k <;> rfl

theorem divideCleanup_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w remainder quotient : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg (discardCoreRenaming .work2)
      FullInterpreterState.moveLens returnLabel
      (discardCfg .done []) state
      (divideAfterFirstCleanupStacks w remainder quotient m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (operandBoundaryBase w quotient m base) := by
  simp [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    discardCoreRenaming, discardCfg, discardStacks,
    divideAfterFirstCleanupStacks, operandBoundaryBase, renamedStacks]
  funext k
  cases k <;> rfl

theorem fullDivideClean_zero_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    ∃ finalState,
      FullInterpreterState.moveLens.get finalState = default ∧
      FullInterpreterState.literalLens.get finalState =
        FullInterpreterState.literalLens.get state ∧
      ((fun o => o.bind (TM2.step
        (fullDivideCleanProgram returnLabel right)))^[
          divZeroRunTime w + 2 * w + 7])
        (some (lensRenamedCfg preparedDivRenaming FullInterpreterState.divLens
          (sparseDivLocalInitialCfg (fixedBits w a).reverse
            (fixedBits (w + 1) 0) (fixedBits (w + 1) 0))
          state (preparedDivideStacks w a 0 m base))) =
      some (mapLabelCfg (fun l : DivideCleanupTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l : DivideCleanupFinalLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w 0 m base))))) := by
  have hcore := fullDivideCore_zero_correct
    (Sum.inl DiscardLabel.loop : DivideCleanupTailLabel R)
    (divideCleanupTailProgram returnLabel right) w a m base state
  let coreState := FullInterpreterState.divLens.put state
    { (default : DivControl) with divisorNonzero := false }
  rw [divideFirstCleanup_bridge (R := R) w 0 0 0 m base coreState
    (by simpa [coreState] using hmove)] at hcore
  have hfirstRaw := run_lensPhase_to_right (discardCoreRenaming .work1)
    FullInterpreterState.moveLens discardProgram .done (by rfl)
    (Sum.inl DiscardLabel.loop) (divideCleanupFinalProgram returnLabel right)
    (discard_correct ((fixedBits (w + 1) 0).map SparseSymbol.bit)) rfl
    coreState (divideCoreResultStacks w 0 0 0 m base)
  simp only [List.length_map, fixedBits_length] at hfirstRaw
  rw [divideSecondCleanup_bridge (R := R) w 0 0 m base coreState] at hfirstRaw
  let firstState := FullInterpreterState.moveLens.put coreState default
  have hsecondRaw := run_lensPhase_to_right (discardCoreRenaming .work2)
    FullInterpreterState.moveLens discardProgram .done (by rfl)
    returnLabel right
    (discard_correct ((fixedBits (w + 1) 0).map SparseSymbol.bit)) rfl
    firstState (divideAfterFirstCleanupStacks w 0 0 m base)
  simp only [List.length_map, fixedBits_length] at hsecondRaw
  rw [divideCleanup_return_bridge returnLabel w 0 0 m base firstState]
    at hsecondRaw
  have hcleanup := chain_liftRightProgram (m := w + 3) (n := w + 3)
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl DiscardLabel.loop))
    (divideCleanupFinalProgram returnLabel right) hfirstRaw hsecondRaw
  have hcleanup' :
      ((fun o => o.bind (TM2.step
        (divideCleanupTailProgram returnLabel right)))^[2 * w + 6])
        (some (lensRenamedCfg (discardCoreRenaming .work1)
          FullInterpreterState.moveLens
          (discardCfg .loop ((fixedBits (w + 1) 0).map SparseSymbol.bit))
          coreState (divideCoreResultStacks w 0 0 0 m base))) =
      some (mapLabelCfg (fun l : DivideCleanupFinalLabel R => Sum.inr l)
        (mapLabelCfg (fun l : R => Sum.inr l)
          (cleanReturnCfg returnLabel
            (FullInterpreterState.moveLens.put firstState default)
            (operandBoundaryBase w 0 m base)))) := by
    simpa only [divideCleanupTailProgram,
      show w + 3 + (w + 3) = 2 * w + 6 by omega] using hcleanup
  have hall := chain_liftRightProgram
    (m := divZeroRunTime w + 1) (n := 2 * w + 6)
    (lensPhaseLeft preparedDivRenaming FullInterpreterState.divLens
      sparseDivCoreProgram .done (Sum.inl DiscardLabel.loop))
    (divideCleanupTailProgram returnLabel right) hcore hcleanup'
  refine ⟨FullInterpreterState.moveLens.put firstState default,
    FullInterpreterState.moveLens.get_put _ _, by rfl, ?_⟩
  have ht : divZeroRunTime w + 2 * w + 7 =
      (divZeroRunTime w + 1) + (2 * w + 6) := by omega
  rw [ht]
  simpa [fullDivideCleanProgram, coreState, firstState] using hall

theorem fullDivideClean_positive_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d : Nat) (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    ∃ finalState,
      FullInterpreterState.moveLens.get finalState = default ∧
      FullInterpreterState.literalLens.get finalState =
        FullInterpreterState.literalLens.get state ∧
      ((fun o => o.bind (TM2.step
        (fullDivideCleanProgram returnLabel right)))^[
          divPositiveRunTime w + 2 * w + 7])
        (some (lensRenamedCfg preparedDivRenaming FullInterpreterState.divLens
          (sparseDivLocalInitialCfg (fixedBits w a).reverse
            (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
          state (preparedDivideStacks w a d m base))) =
      some (mapLabelCfg (fun l : DivideCleanupTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l : DivideCleanupFinalLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w (a / d) m base))))) := by
  have hcore := fullDivideCore_positive_correct
    (Sum.inl DiscardLabel.loop : DivideCleanupTailLabel R)
    (divideCleanupTailProgram returnLabel right) w a d ha hd0 hd m base state
  let coreState := FullInterpreterState.divLens.put state
    { (default : DivControl) with divisorNonzero := true }
  rw [divideFirstCleanup_bridge (R := R) w d (a % d) (a / d) m base coreState
    (by simpa [coreState] using hmove)]
    at hcore
  have hfirstRaw := run_lensPhase_to_right (discardCoreRenaming .work1)
    FullInterpreterState.moveLens discardProgram .done (by rfl)
    (Sum.inl DiscardLabel.loop) (divideCleanupFinalProgram returnLabel right)
    (discard_correct ((fixedBits (w + 1) d).map SparseSymbol.bit)) rfl
    coreState (divideCoreResultStacks w d (a % d) (a / d) m base)
  simp only [List.length_map, fixedBits_length] at hfirstRaw
  have hbridge : phaseReturnCfg (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (Sum.inl DiscardLabel.loop : DivideCleanupFinalLabel R)
      (discardCfg .done []) coreState
      (divideCoreResultStacks w d (a % d) (a / d) m base) =
    lensRenamedCfg (discardCoreRenaming .work2)
      FullInterpreterState.moveLens
      (discardCfg .loop ((fixedBits (w + 1) (a % d)).map SparseSymbol.bit))
      (FullInterpreterState.moveLens.put coreState default)
      (divideAfterFirstCleanupStacks w (a % d) (a / d) m base) := by
    simp [phaseReturnCfg, lensRenamedCfg, discardCoreRenaming, discardCfg,
      discardStacks, divideCoreResultStacks, divideAfterFirstCleanupStacks,
      renamedStacks]
    constructor
    · rfl
    · funext k
      cases k <;> rfl
  rw [hbridge] at hfirstRaw
  let firstState := FullInterpreterState.moveLens.put coreState default
  have hsecondRaw := run_lensPhase_to_right (discardCoreRenaming .work2)
    FullInterpreterState.moveLens discardProgram .done (by rfl)
    returnLabel right
    (discard_correct ((fixedBits (w + 1) (a % d)).map SparseSymbol.bit)) rfl
    firstState (divideAfterFirstCleanupStacks w (a % d) (a / d) m base)
  simp only [List.length_map, fixedBits_length] at hsecondRaw
  rw [divideCleanup_return_bridge returnLabel w (a % d) (a / d) m base firstState]
    at hsecondRaw
  have hcleanup := chain_liftRightProgram (m := w + 3) (n := w + 3)
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl DiscardLabel.loop))
    (divideCleanupFinalProgram returnLabel right) hfirstRaw hsecondRaw
  have hcleanup' :
      ((fun o => o.bind (TM2.step
        (divideCleanupTailProgram returnLabel right)))^[2 * w + 6])
        (some (lensRenamedCfg (discardCoreRenaming .work1)
          FullInterpreterState.moveLens
          (discardCfg .loop ((fixedBits (w + 1) d).map SparseSymbol.bit))
          coreState (divideCoreResultStacks w d (a % d) (a / d) m base))) =
      some (mapLabelCfg (fun l : DivideCleanupFinalLabel R => Sum.inr l)
        (mapLabelCfg (fun l : R => Sum.inr l)
          (cleanReturnCfg returnLabel
            (FullInterpreterState.moveLens.put firstState default)
            (operandBoundaryBase w (a / d) m base)))) := by
    simpa only [divideCleanupTailProgram,
      show w + 3 + (w + 3) = 2 * w + 6 by omega] using hcleanup
  have hall := chain_liftRightProgram
    (m := divPositiveRunTime w + 1) (n := 2 * w + 6)
    (lensPhaseLeft preparedDivRenaming FullInterpreterState.divLens
      sparseDivCoreProgram .done (Sum.inl DiscardLabel.loop))
    (divideCleanupTailProgram returnLabel right) hcore hcleanup'
  refine ⟨FullInterpreterState.moveLens.put firstState default,
    FullInterpreterState.moveLens.get_put _ _, by rfl, ?_⟩
  have ht : divPositiveRunTime w + 2 * w + 7 =
      (divPositiveRunTime w + 1) + (2 * w + 6) := by omega
  rw [ht]
  simpa [fullDivideCleanProgram, coreState, firstState] using hall

end Lax20Proofs.RamToTM
