import Lax51Proofs.RamToTM.FiniteDispatcher

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

noncomputable section

def PreservesDispatch {N : Nat} {L : Type}
    (stmt : TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)) : Prop :=
  ∀ state tapes, FullInterpreterState.dispatchLens.get
    (TM2.stepAux stmt state tapes).var =
    FullInterpreterState.dispatchLens.get state

def ProgramPreservesDispatch {N : Nat} {I L : Type}
    (program : I -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)) : Prop :=
  ∀ label, PreservesDispatch (program label)

def StmtPreservesDispatch {N : Nat} {L : Type} :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N) → Prop
  | .push _ _ q => StmtPreservesDispatch q
  | .peek _ f q =>
      (∀ s a, (f s a).dispatch = s.dispatch) ∧ StmtPreservesDispatch q
  | .pop _ f q =>
      (∀ s a, (f s a).dispatch = s.dispatch) ∧ StmtPreservesDispatch q
  | .load f q =>
      (∀ s, (f s).dispatch = s.dispatch) ∧ StmtPreservesDispatch q
  | .branch _ q₁ q₂ => StmtPreservesDispatch q₁ ∧ StmtPreservesDispatch q₂
  | .goto _ | .halt => True

theorem StmtPreservesDispatch.sound {N : Nat} {L : Type}
    {q : TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)} (hq : StmtPreservesDispatch q) :
    PreservesDispatch q := by
  intro state tapes
  induction q generalizing state tapes with
  | push k f q ih =>
      simpa only [TM2.stepAux] using
        ih hq state (Function.update tapes k (f state :: tapes k))
  | peek k f q ih =>
      exact (ih hq.2 (f state (tapes k).head?) tapes).trans (hq.1 state _)
  | pop k f q ih =>
      exact (ih hq.2 (f state (tapes k).head?)
        (Function.update tapes k (tapes k).tail)).trans (hq.1 state _)
  | load f q ih =>
      exact (ih hq.2 (f state) tapes).trans (hq.1 state)
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases h : f state <;> simp [TM2.stepAux, h]
      · exact ih₂ hq.2 state tapes
      · exact ih₁ hq.1 state tapes
  | goto f => rfl
  | halt => rfl

theorem PreservesDispatch.mapLabelStmt {N : Nat} {L L' : Type}
    (encode : L → L')
    {q : TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)} (hq : PreservesDispatch q) :
    PreservesDispatch (mapLabelStmt encode q) := by
  intro state tapes
  rw [stepAux_mapLabelStmt]
  exact hq state tapes

theorem PreservesDispatch.lensRenameStmt
    {N : Nat} {K L X σ : Type} [DecidableEq K]
    (stackMap : StackRenaming K CoreStack)
    (lens : StateLens σ (FullInterpreterState N))
    (hdisjoint : ∀ s v, (lens.put s v).dispatch = s.dispatch)
    (q : TM2.Stmt (fun _ : K => SparseSymbol) L σ) :
    PreservesDispatch (lensRenameStmt (Λx := X) stackMap lens q) := by
  intro state tapes
  induction q generalizing state tapes with
  | push k f q ih =>
      simpa only [lensRenameStmt, TM2.stepAux] using
        ih state (Function.update tapes (stackMap.encode k)
          (f (lens.get state) :: tapes (stackMap.encode k)))
  | peek k f q ih =>
      exact (ih (lens.put state (f (lens.get state)
        (tapes (stackMap.encode k)).head?)) tapes).trans
          (hdisjoint state _)
  | pop k f q ih =>
      exact (ih (lens.put state (f (lens.get state)
        (tapes (stackMap.encode k)).head?))
          (Function.update tapes (stackMap.encode k)
            (tapes (stackMap.encode k)).tail)).trans
          (hdisjoint state _)
  | load f q ih =>
      exact (ih (lens.put state (f (lens.get state))) tapes).trans
        (hdisjoint state _)
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases h : f (lens.get state)
      · simpa only [Lax51Proofs.RamToTM.lensRenameStmt, TM2.stepAux, h] using
          ih₂ state tapes
      · simpa only [Lax51Proofs.RamToTM.lensRenameStmt, TM2.stepAux, h] using
          ih₁ state tapes
  | goto f => rfl
  | halt => rfl

theorem PreservesDispatch.lensPhaseLeft
    {N : Nat} {K L R σ : Type} [DecidableEq K] [DecidableEq L]
    (stackMap : StackRenaming K CoreStack)
    (lens : StateLens σ (FullInterpreterState N))
    (hdisjoint : ∀ s v, (lens.put s v).dispatch = s.dispatch)
    (program : L → TM2.Stmt (fun _ : K => SparseSymbol) L σ)
    (done : L) (entry : R) (label : L) :
    PreservesDispatch (lensPhaseLeft stackMap lens program done entry label) := by
  unfold Lax51Proofs.RamToTM.lensPhaseLeft
  split
  · intro state tapes
    rfl
  · exact PreservesDispatch.lensRenameStmt (X := R)
      stackMap lens hdisjoint (program label)

theorem ProgramPreservesDispatch.lensPhaseLeft
    {N : Nat} {K L R σ : Type} [DecidableEq K] [DecidableEq L]
    (stackMap : StackRenaming K CoreStack)
    (lens : StateLens σ (FullInterpreterState N))
    (hdisjoint : ∀ s v, (lens.put s v).dispatch = s.dispatch)
    (program : L → TM2.Stmt (fun _ : K => SparseSymbol) L σ)
    (done : L) (entry : R) :
    ProgramPreservesDispatch
      (lensPhaseLeft stackMap lens program done entry) := by
  intro label
  exact PreservesDispatch.lensPhaseLeft stackMap lens hdisjoint
    program done entry label

theorem ProgramPreservesDispatch.liftRightProgram
    {N : Nat} {L R : Type}
    (left : L → TM2.Stmt (fun _ : CoreStack => SparseSymbol) (Sum L R)
      (FullInterpreterState N))
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (hleft : ProgramPreservesDispatch left)
    (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (liftRightProgram left right) := by
  intro label
  cases label with
  | inl label =>
      change PreservesDispatch (left label)
      exact hleft label
  | inr label =>
      exact PreservesDispatch.mapLabelStmt Sum.inr (hright label)

theorem ProgramPreservesDispatch.lensMultiPhaseLeft
    {N : Nat} {K L R σ : Type} [DecidableEq K]
    (stackMap : StackRenaming K CoreStack)
    (lens : StateLens σ (FullInterpreterState N))
    (hdisjoint : ∀ s v, (lens.put s v).dispatch = s.dispatch)
    (program : L → TM2.Stmt (fun _ : K => SparseSymbol) L σ)
    (exit : L → Option R)
    (onExit : L → FullInterpreterState N → FullInterpreterState N)
    (hexit : ∀ label state, (onExit label state).dispatch = state.dispatch) :
    ProgramPreservesDispatch
      (lensMultiPhaseLeft stackMap lens program exit onExit) := by
  intro label
  unfold Lax51Proofs.RamToTM.lensMultiPhaseLeft
  cases h : exit label with
  | none =>
      exact PreservesDispatch.lensRenameStmt (X := R)
        stackMap lens hdisjoint (program label)
  | some next =>
      intro state tapes
      simpa only [TM2.stepAux] using hexit label state

theorem haltProgram_preservesDispatch {N : Nat} {L : Type} :
    ProgramPreservesDispatch
      (fun _ : L => (.halt : TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
        (FullInterpreterState N))) := by
  intro label state tapes
  rfl

theorem fullLoadProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (fullLoadProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft coreIdentityRenaming
      FullInterpreterState.macroLens (by intros; rfl)
      closedAccInstallProgram closedAccInstallDone
      (Sum.inl DiscardLabel.loop)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft
        (discardCoreRenaming .work7) FullInterpreterState.moveLens
        (by intros; rfl) discardProgram .done returnLabel
    · exact hright

theorem loadResetProgram_preservesDispatch {N : Nat} {R : Type} :
    ProgramPreservesDispatch (loadResetProgram (N := N) (R := R)) := by
  intro label
  cases label
  intro state tapes
  rfl

theorem loadInstructionTailProgram_preservesDispatch
    {N : Nat} {R : Type} (returnLabel : R) :
    ProgramPreservesDispatch
      (loadInstructionTailProgram (N := N) returnLabel (fun _ => .halt)) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact loadResetProgram_preservesDispatch
  · exact fullLoadProgram_preservesDispatch returnLabel _
      haltProgram_preservesDispatch

theorem unifiedLookupProgram_preservesDispatch {N : Nat} {R : Type}
    (right : UnifiedLookupTail R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (UnifiedLookupTail R)
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (unifiedLookupProgram right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensMultiPhaseLeft lookupCoreRenaming
      FullInterpreterState.lookupLens (by intros; rfl)
      lookupScanProgram lookupExit lookupRecordOutcome (by intros; rfl)
  · exact hright

theorem lookupDecisionProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) :
    ProgramPreservesDispatch
      (lookupDecisionProgram (N := N) returnLabel) := by
  intro label
  cases label
  intro state tapes
  cases h : state.lookupFound <;>
    simp [lookupDecisionProgram, TM2.stepAux, h]

theorem unifiedCleanFinishProgram_preservesDispatch
    {N : Nat} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch
      (unifiedCleanFinishProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft zeroWordCoreRenaming
      FullInterpreterState.zeroLens (by intros; rfl)
      zeroWordProgram .done returnLabel
  · exact hright

theorem unifiedCleanLookupProgram_preservesDispatch
    {N : Nat} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch
      (unifiedCleanLookupProgram returnLabel right) := by
  apply unifiedLookupProgram_preservesDispatch
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (discardCoreRenaming .work1) FullInterpreterState.moveLens
      (by intros; rfl) discardProgram .done
      (Sum.inl LookupDecisionLabel.decide)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact lookupDecisionProgram_preservesDispatch returnLabel
    · exact unifiedCleanFinishProgram_preservesDispatch returnLabel right hright

theorem lookupInitProgram_preservesDispatch {N : Nat} {R : Type} :
    ProgramPreservesDispatch (lookupInitProgram (N := N) (R := R)) := by
  intro label
  cases label
  intro state tapes
  simp [lookupInitProgram, FullInterpreterState.lookupLens,
    FullInterpreterState.dispatchLens, FullInterpreterState.macroLens,
    InterpreterMacroState.lookupLens, StateLens.comp, TM2.stepAux]

theorem directOperandProgram_preservesDispatch
    {N : Nat} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (directOperandProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft literalQueryCoreRenaming
      FullInterpreterState.literalLens (by intros; rfl)
      (boundedLiteralWordProgram N) .done (Sum.inl LookupInitLabel.init)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact lookupInitProgram_preservesDispatch
    · exact unifiedCleanLookupProgram_preservesDispatch returnLabel right hright

theorem queryTransferProgram_preservesDispatch
    {N : Nat} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (queryTransferProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens (by intros; rfl)
      symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft
        (symbolMoveCoreRenaming .work2 .work1 (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        symbolMoveCoreProgram .done returnLabel
    · exact hright

theorem indirectOperandProgram_preservesDispatch
    {N : Nat} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (indirectOperandProgram returnLabel right) := by
  apply directOperandProgram_preservesDispatch
  apply queryTransferProgram_preservesDispatch
  apply ProgramPreservesDispatch.liftRightProgram
  · exact lookupInitProgram_preservesDispatch
  · exact unifiedCleanLookupProgram_preservesDispatch returnLabel right hright

theorem literalOperandProgram_preservesDispatch
    {N : Nat} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (literalOperandProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft literalWordCoreRenaming
      FullInterpreterState.literalLens (by intros; rfl)
      (boundedLiteralWordProgram N) .done returnLabel
  · exact hright

theorem operandEvalProgram_preservesDispatch
    {N : Nat} {R : Type} (o : Op) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (operandEvalProgram o returnLabel right) := by
  cases o with
  | lit n => exact literalOperandProgram_preservesDispatch returnLabel right hright
  | mem a => exact directOperandProgram_preservesDispatch returnLabel right hright
  | ind a => exact indirectOperandProgram_preservesDispatch returnLabel right hright

theorem fullAddPhaseProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (fullAddPhaseProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft coreIdentityRenaming
      FullInterpreterState.macroLens (by intros; rfl)
      closedAddPipelineProgram closedAddDone returnLabel
  · exact hright

theorem addInstructionTailProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (addInstructionTailProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes; rfl
  · exact fullAddPhaseProgram_preservesDispatch returnLabel right hright

theorem fullCopyProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (fullCopyProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide) (by decide))
      FullInterpreterState.moveLens (by intros; rfl) copyProgram .done returnLabel
  · exact hright

theorem fullPrependProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (fullPrependProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft prependCoreRenaming
      FullInterpreterState.prependLens (by intros; rfl)
      prependCoreProgram .done returnLabel
  · exact hright

theorem storeInstructionTailProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (storeInstructionTailProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes; rfl
  · apply fullCopyProgram_preservesDispatch
    apply ProgramPreservesDispatch.liftRightProgram
    · intro label; cases label; intro state tapes; rfl
    · exact fullPrependProgram_preservesDispatch returnLabel right hright

theorem readTransferProgram_preservesDispatch {N : Nat} {R : Type}
    (exhaustedLabel returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (readTransferProgram exhaustedLabel returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label
    apply StmtPreservesDispatch.sound
    cases label <;>
      simp [StmtPreservesDispatch, readTransferLeftProgram,
        FullInterpreterState.moveLens, FullInterpreterState.prependLens,
        FullInterpreterState.dispatchLens, FullInterpreterState.macroLens,
        InterpreterMacroState.moveLens, InterpreterMacroState.prependLens,
        StateLens.comp]
  · exact fullPrependProgram_preservesDispatch returnLabel right hright

theorem writeTailProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (writeTailProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes; rfl
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
    · apply ProgramPreservesDispatch.liftRightProgram
      · exact ProgramPreservesDispatch.lensPhaseLeft
          (symbolMoveCoreRenaming .work1 .output (by decide))
          FullInterpreterState.moveLens (by intros; rfl)
          symbolMoveCoreProgram .done (Sum.inl WriteFinishLabel.finish)
      · apply ProgramPreservesDispatch.liftRightProgram
        · intro label; cases label; intro state tapes; rfl
        · exact hright

theorem fullSubtractProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (fullSubtractProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens (by intros; rfl)
      symbolMoveCoreProgram .done (Sum.inl AddLabel.loop)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft binaryCoreRenaming
        FullInterpreterState.subLens (by intros; rfl)
        sparseSubCoreProgram .done (Sum.inl ConditionalInstallLabel.loop)
    · apply ProgramPreservesDispatch.liftRightProgram
      · intro label state tapes
        cases label
        · simp [lensPhaseLeft, lensRenameStmt, conditionalInstallProgram,
            fullStateIdentityLens, coreIdentityRenaming, TM2.stepAux]
          generalize
            (FullInterpreterState.moveLens.get
              (FullInterpreterState.moveLens.put state
                { held := (tapes .work0).head? })).held.isNone = b
          cases b <;> rfl
        · rfl
      · exact hright

theorem subtractInstructionTailProgram_preservesDispatch {N : Nat} {R : Type}
    (o : Op) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (subtractInstructionTailProgram o returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes; rfl
  · exact fullSubtractProgram_preservesDispatch returnLabel right hright

theorem fullMulProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (fullMulProgram returnLabel right) := by
  letI : DecidableEq ClosedMulLabel := Classical.decEq _
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft coreIdentityRenaming
      FullInterpreterState.macroLens (by intros; rfl)
      closedMulProgram closedMulDone (Sum.inl DiscardLabel.loop)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft (discardCoreRenaming .work7)
        FullInterpreterState.moveLens (by intros; rfl)
        discardProgram .done returnLabel
    · exact hright

theorem mulInstructionTailProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (mulInstructionTailProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes; rfl
  · exact fullMulProgram_preservesDispatch returnLabel right hright

theorem zipInstructionTailProgram_preservesDispatch {N : Nat} {R : Type}
    (f : Bool → Bool → Bool) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (zipInstructionTailProgram f returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes; rfl
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft coreIdentityRenaming
        FullInterpreterState.macroLens (by intros; rfl)
        (closedZipProgram f) closedZipDone returnLabel
    · exact hright

theorem fullDivideCleanProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (fullDivideCleanProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft preparedDivRenaming
      FullInterpreterState.divLens (by intros; rfl)
      sparseDivCoreProgram .done (Sum.inl DiscardLabel.loop)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft (discardCoreRenaming .work1)
        FullInterpreterState.moveLens (by intros; rfl)
        discardProgram .done (Sum.inl DiscardLabel.loop)
    · apply ProgramPreservesDispatch.liftRightProgram
      · exact ProgramPreservesDispatch.lensPhaseLeft (discardCoreRenaming .work2)
          FullInterpreterState.moveLens (by intros; rfl)
          discardProgram .done returnLabel
      · exact hright

theorem fullDivideProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (fullDivideProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes
    simp [dividePrepareProgram, dividePrepareReset, TM2.stepAux,
      FullInterpreterState.moveLens, FullInterpreterState.zeroLens,
      FullInterpreterState.divLens, FullInterpreterState.dispatchLens,
      FullInterpreterState.macroLens, InterpreterMacroState.moveLens,
      InterpreterMacroState.divLens, StateLens.comp]
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
    · apply ProgramPreservesDispatch.liftRightProgram
      · exact ProgramPreservesDispatch.lensPhaseLeft
          (symbolMoveCoreRenaming .accumulator .work7 (by decide))
          FullInterpreterState.moveLens (by intros; rfl)
          symbolMoveCoreProgram .done (Sum.inl ZeroWordLabel.fill)
      · apply ProgramPreservesDispatch.liftRightProgram
        · exact ProgramPreservesDispatch.lensPhaseLeft divideZeroRenaming
            FullInterpreterState.zeroLens (by intros; rfl)
            zeroWordProgram .done (Sum.inl DivLabel.inspectDivisor)
        · exact fullDivideCleanProgram_preservesDispatch returnLabel right hright

theorem conditionalZeroProgram_preservesDispatch {N : Nat} (o : Op) :
    ProgramPreservesDispatch (conditionalZeroProgram N o) := by
  intro label state tapes
  cases label
  · simp only [conditionalZeroProgram, TM2.stepAux]
    generalize hb :
      (FullInterpreterState.moveLens.get
        (FullInterpreterState.moveLens.put state
          { held := (tapes .accumulator).head? })).held.isNone = b
    cases b <;> simp [hb, FullInterpreterState.moveLens,
      FullInterpreterState.dispatchLens, FullInterpreterState.macroLens,
      InterpreterMacroState.moveLens, StateLens.comp]
  · rfl

theorem conditionalZeroPhaseProgram_preservesDispatch {N : Nat} {R : Type}
    (o : Op) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (conditionalZeroPhaseProgram o returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label
    unfold lensPhaseLeft
    split
    · intro state tapes; rfl
    · apply StmtPreservesDispatch.sound
      cases label <;>
        simp [StmtPreservesDispatch, lensRenameStmt, conditionalZeroProgram,
          fullStateIdentityLens, coreIdentityRenaming,
          FullInterpreterState.moveLens, FullInterpreterState.dispatchLens,
          FullInterpreterState.macroLens, InterpreterMacroState.moveLens,
          StateLens.comp]
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        symbolMoveCoreProgram .done returnLabel
    · exact hright

theorem fullDividePostProgram_preservesDispatch {N : Nat} {R : Type}
    (o : Op) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (fullDividePostProgram o returnLabel right) := by
  exact fullDivideProgram_preservesDispatch _ _
    (conditionalZeroPhaseProgram_preservesDispatch o returnLabel right hright)

theorem shiftRoundFinalProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (shiftRoundFinalProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens (by intros; rfl)
      symbolMoveCoreProgram .done returnLabel
  · exact hright

theorem shiftLeftRoundTailProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (shiftLeftRoundTailProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens (by intros; rfl)
      symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
  · exact shiftRoundFinalProgram_preservesDispatch returnLabel right hright

theorem shiftLeftRoundProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (shiftLeftRoundProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft shiftRoundRenaming
      FullInterpreterState.shiftLens (by intros; rfl)
      sparseShiftLeftCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
  · exact shiftLeftRoundTailProgram_preservesDispatch returnLabel right hright

theorem shiftRightRoundProgram_preservesDispatch {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (shiftRightRoundProgram returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft shiftRoundRenaming
      FullInterpreterState.shiftLens (by intros; rfl)
      sparseShiftRightCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
  · exact shiftLeftRoundTailProgram_preservesDispatch returnLabel right hright

theorem fullShiftProgram_preservesDispatch {N : Nat} {R : Type}
    (o : Op) (rightShift : Bool) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright : ProgramPreservesDispatch right) :
    ProgramPreservesDispatch (fullShiftProgram o rightShift returnLabel right) := by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label
    cases label
    · apply PreservesDispatch.mapLabelStmt Sum.inl
      apply StmtPreservesDispatch.sound
      simp [StmtPreservesDispatch, shiftSetupProgram, resetShiftControls,
        FullInterpreterState.dispatchLens, FullInterpreterState.macroLens,
        FullInterpreterState.moveLens, FullInterpreterState.shiftLens,
        FullInterpreterState.countdownLens,
        InterpreterMacroState.dispatchLens, InterpreterMacroState.moveLens,
        StateLens.comp]
    · rename_i label
      apply PreservesDispatch.mapLabelStmt Sum.inl
      apply PreservesDispatch.mapLabelStmt embedSetupMove
      exact PreservesDispatch.lensPhaseLeft
        (symbolMoveCoreRenaming .work0 .work3 (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        symbolMoveCoreProgram .done () label
    · rename_i label
      apply PreservesDispatch.mapLabelStmt Sum.inl
      apply PreservesDispatch.mapLabelStmt embedSetupCopy
      exact PreservesDispatch.lensPhaseLeft
        (copyCoreRenaming .accumulator .work1 .work7
          (by decide) (by decide) (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        copyProgram .done () label
    · rename_i label
      cases label with
      | countdown label =>
          simp only [fullShiftLeft, shiftSetupProgram, cappedShiftProgram]
          apply PreservesDispatch.mapLabelStmt Sum.inl
          apply PreservesDispatch.mapLabelStmt ShiftSetupLabel.controller
          apply PreservesDispatch.mapLabelStmt embedCountdownController
          exact (ProgramPreservesDispatch.lensMultiPhaseLeft
            countdownCoreRenaming FullInterpreterState.countdownLens
            (by intros; rfl) sparseCountdownProgram
            (countdownExit CappedShiftLabel.cleanupFuel CappedShiftLabel.fuel)
            countdownOnExit (by intros; rfl)) label
      | left label =>
        by_cases h : label = Sum.inr (Sum.inr (Sum.inr ()))
        · subst label
          apply StmtPreservesDispatch.sound
          simp [StmtPreservesDispatch, fullShiftLeft, shiftSetupProgram,
            cappedShiftProgram, mapLabelStmt, FullInterpreterState.countdownLens,
            FullInterpreterState.dispatchLens, FullInterpreterState.macroLens,
            StateLens.comp]
        · simp only [fullShiftLeft, shiftSetupProgram, cappedShiftProgram, h]
          apply PreservesDispatch.mapLabelStmt Sum.inl
          apply PreservesDispatch.mapLabelStmt ShiftSetupLabel.controller
          apply PreservesDispatch.mapLabelStmt CappedShiftLabel.left
          exact shiftLeftRoundProgram_preservesDispatch () (fun _ => .halt)
            (by intro u; cases u; intro state tapes; rfl) label
      | right label =>
        by_cases h : label = Sum.inr (Sum.inr (Sum.inr ()))
        · subst label
          apply StmtPreservesDispatch.sound
          simp [StmtPreservesDispatch, fullShiftLeft, shiftSetupProgram,
            cappedShiftProgram, mapLabelStmt, FullInterpreterState.countdownLens,
            FullInterpreterState.dispatchLens, FullInterpreterState.macroLens,
            StateLens.comp]
        · simp only [fullShiftLeft, shiftSetupProgram, cappedShiftProgram, h]
          apply PreservesDispatch.mapLabelStmt Sum.inl
          apply PreservesDispatch.mapLabelStmt ShiftSetupLabel.controller
          apply PreservesDispatch.mapLabelStmt CappedShiftLabel.right
          exact shiftRightRoundProgram_preservesDispatch () (fun _ => .halt)
            (by intro u; cases u; intro state tapes; rfl) label
      | fuel | cleanupFuel | cleanupCount | cleanupTemp | done =>
        apply StmtPreservesDispatch.sound
        simp [StmtPreservesDispatch, fullShiftLeft, shiftSetupProgram,
          cappedShiftProgram, cappedShiftCleanupStmt, resetShiftControls, mapLabelStmt,
          countdownMultiLeft, lensMultiPhaseLeft, lensRenameStmt,
          sparseCountdownProgram, countdownExit, countdownOnExit,
          FullInterpreterState.dispatchLens, FullInterpreterState.macroLens,
          FullInterpreterState.moveLens, FullInterpreterState.shiftLens,
          FullInterpreterState.countdownLens,
          InterpreterMacroState.dispatchLens, InterpreterMacroState.moveLens,
          StateLens.comp]
  · exact conditionalZeroPhaseProgram_preservesDispatch o returnLabel right hright

theorem iterate_preservesDispatch {N n : Nat} {L : Type}
    (program : L -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (hprogram : ProgramPreservesDispatch program)
    (c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (hrun : ((fun x => x.bind (TM2.step program))^[n]) (some c) = some d) :
    FullInterpreterState.dispatchLens.get d.var =
      FullInterpreterState.dispatchLens.get c.var := by
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hrun
      subst d
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun
      simp only [Option.bind_some] at hrun
      cases hs : TM2.step program c with
      | none =>
          rw [hs, iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          rw [hs] at hrun
          rcases c with ⟨label, state, tapes⟩
          cases label with
          | none => simp [TM2.step] at hs
          | some label =>
              simp only [TM2.step] at hs
              have hc' := Option.some.inj hs
              subst c'
              exact (ih _ hrun).trans (hprogram label state tapes)

theorem operandBoundaryBase_coreStacks_withMemory (w value : Nat)
    (m : SparseMemory) (s : SparseState) :
    operandBoundaryBase w value m (coreStacks w s) =
      coreStacks w {s with acc := value, mem := m} := by
  funext k
  cases k <;> rfl

theorem transport_finiteLocal_cfg_to_fetch_selective
    {p : Program} {N n : Nat} {L : Type} [Fintype L]
    (encode : L → FiniteInterpreterLabel p N) (next : BoundedPC p)
    (program : L → TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (target : FiniteInterpreterLabel p N → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N))
    (hnonhalt : ∀ label, program label ≠ .halt →
      target (encode label) = mapLabelStmt encode (program label))
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)}
    (hrun : ((fun x => x.bind (TM2.step program))^[n]) (some c) = some d)
    (hd : d.l.isSome) (hhalt : program (d.l.get hd) = .halt)
    (hfinal : target (encode (d.l.get hd)) = .goto (fun _ => .fetch next)) :
    ((fun x => x.bind (TM2.step target))^[n + 1])
      (some (finiteEmbedCfg encode c)) =
      some (finiteInterpreterCfg (.fetch next) d.var d.stk) := by
  have htransport := iterate_mapLabelProgram_until_exit program target encode
    hnonhalt hrun hd
  have hembed : finiteEmbedCfg encode d =
      finiteInterpreterCfg (encode (d.l.get hd)) d.var d.stk := by
    rcases d with ⟨label, state, tapes⟩
    cases label with
    | none => simp at hd
    | some label => rfl
  have htransport' :
      ((fun x => x.bind (TM2.step target))^[n])
        (some (finiteEmbedCfg encode c)) =
      some (finiteInterpreterCfg (encode (d.l.get hd)) d.var d.stk) := by
    exact htransport.trans (congrArg some hembed)
  have hexit :
      ((fun x => x.bind (TM2.step target))^[1])
        (some (finiteInterpreterCfg (encode (d.l.get hd)) d.var d.stk)) =
      some (finiteInterpreterCfg (.fetch next) d.var d.stk) := by
    simp [hfinal, finiteInterpreterCfg, TM2.step]
  exact chain_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step target)) htransport' hexit

theorem loadInstructionProgram_preservesDispatch {N : Nat} {R : Type}
    (o : Op) (returnLabel : R) :
    ProgramPreservesDispatch
      (loadInstructionProgram (N := N) o returnLabel (fun _ => .halt)) := by
  exact operandEvalProgram_preservesDispatch o _ _
    (loadInstructionTailProgram_preservesDispatch returnLabel)

theorem addInstructionProgram_preservesDispatch {N : Nat} {R : Type}
    (o : Op) (returnLabel : R) :
    ProgramPreservesDispatch
      (addInstructionProgram (N := N) o returnLabel (fun _ => .halt)) := by
  exact operandEvalProgram_preservesDispatch o _ _
    (addInstructionTailProgram_preservesDispatch returnLabel _
      haltProgram_preservesDispatch)

theorem writeInstructionProgram_preservesDispatch {N : Nat} {R : Type}
    (o : Op) (returnLabel : R) :
    ProgramPreservesDispatch
      (writeInstructionProgram (N := N) o returnLabel (fun _ => .halt)) := by
  exact operandEvalProgram_preservesDispatch o _ _
    (writeTailProgram_preservesDispatch returnLabel _
      haltProgram_preservesDispatch)

theorem storeInstructionProgram_preservesDispatch {N : Nat} {R : Type}
    (address : Nat) (returnLabel : R) :
    ProgramPreservesDispatch
      (storeInstructionProgram (N := N) address returnLabel (fun _ => .halt)) := by
  exact operandEvalProgram_preservesDispatch (.lit address) _ _
    (storeInstructionTailProgram_preservesDispatch returnLabel _
      haltProgram_preservesDispatch)

theorem storeIndInstructionProgram_preservesDispatch {N : Nat} {R : Type}
    (address : Nat) (returnLabel : R) :
    ProgramPreservesDispatch
      (storeIndInstructionProgram (N := N) address returnLabel
        (fun _ => .halt)) := by
  exact operandEvalProgram_preservesDispatch (.mem address) _ _
    (storeInstructionTailProgram_preservesDispatch returnLabel _
      haltProgram_preservesDispatch)

theorem readInstructionProgram_preservesDispatch {N : Nat} {R : Type}
    (address : Nat) (exhaustedLabel returnLabel : R) :
    ProgramPreservesDispatch
      (readInstructionProgram (N := N) address exhaustedLabel returnLabel
        (fun _ => .halt)) := by
  exact operandEvalProgram_preservesDispatch (.lit address) _ _
    (readTransferProgram_preservesDispatch exhaustedLabel returnLabel _
      haltProgram_preservesDispatch)

theorem subtractInstructionProgram_preservesDispatch {N : Nat} {R : Type}
    (o : Op) (returnLabel : R) :
    ProgramPreservesDispatch
      (subtractInstructionProgram (N := N) o returnLabel (fun _ => .halt)) := by
  exact operandEvalProgram_preservesDispatch o _ _
    (subtractInstructionTailProgram_preservesDispatch o returnLabel _
      haltProgram_preservesDispatch)

theorem mulInstructionProgram_preservesDispatch {N : Nat} {R : Type}
    (o : Op) (returnLabel : R) :
    ProgramPreservesDispatch
      (mulInstructionProgram (N := N) o returnLabel (fun _ => .halt)) := by
  exact operandEvalProgram_preservesDispatch o _ _
    (mulInstructionTailProgram_preservesDispatch returnLabel _
      haltProgram_preservesDispatch)

theorem divideInstructionProgram_preservesDispatch {N : Nat} {R : Type}
    (o : Op) (returnLabel : R) :
    ProgramPreservesDispatch
      (divideInstructionTotalProgram (N := N) o returnLabel
        (fun _ => .halt)) := by
  exact operandEvalProgram_preservesDispatch o _ _
    (fullDividePostProgram_preservesDispatch o returnLabel _
      haltProgram_preservesDispatch)

theorem bitwiseInstructionProgram_preservesDispatch {N : Nat} {R : Type}
    (kind : BitwiseKind) (o : Op) (returnLabel : R) :
    ProgramPreservesDispatch
      (bitwiseInstructionProgram (N := N) kind o returnLabel
        (fun _ => .halt)) := by
  exact operandEvalProgram_preservesDispatch o _ _
    (zipInstructionTailProgram_preservesDispatch kind.boolFn returnLabel _
      haltProgram_preservesDispatch)

theorem shiftInstructionProgram_preservesDispatch {N : Nat} {R : Type}
    (rightShift : Bool) (o : Op) (returnLabel : R) :
    ProgramPreservesDispatch
      (shiftInstructionProgram (N := N) o rightShift returnLabel
        (fun _ => .halt)) := by
  exact operandEvalProgram_preservesDispatch o _ _
    (fullShiftProgram_preservesDispatch o rightShift returnLabel _
      haltProgram_preservesDispatch)

theorem finite_data_prefix {p : Program} {N pc n : Nat}
    (hbound : programArgumentBound p <= N) {i : Instr}
    (hfetch : p[pc]? = some i) (hdata : i ≠ .halt)
    (hnjump : match i with
      | .jump _ | .jzero _ | .jgtz _ => False
      | _ => True)
    (state : FullInterpreterState N) (tapes : CoreStack -> List SparseSymbol)
    (localCfg finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N))
    (hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg
        (.control (.data (boundPC p pc) (instrClass i))) state tapes) =
      some localCfg)
    (hlocal : ((fun x => x.bind
      (TM2.step (finiteInterpreterProgram p N hbound)))^[n])
      (some localCfg) = some finalCfg) :
    ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[2 + n])
      (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes)) =
    some finalCfg := by
  have hfetchStep := finite_step_fetch_data hbound hfetch hdata hnjump state tapes
  have hfetchIter :
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[1])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes)) =
      some (finiteInterpreterCfg
        (.control (.data (boundPC p pc) (instrClass i))) state tapes) := by
    simpa using hfetchStep
  have hentryIter :
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[1])
        (some (finiteInterpreterCfg
          (.control (.data (boundPC p pc) (instrClass i))) state tapes)) =
      some localCfg := by
    simpa using hentry
  have hprefix := chain_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step (finiteInterpreterProgram p N hbound)))
    hfetchIter hentryIter
  exact chain_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step (finiteInterpreterProgram p N hbound)))
    hprefix hlocal

theorem finite_load_local_correct {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (o : BoundedOp N) (w : Nat) (s : SparseState) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= loadInstructionBound w s.mem ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeLoadLabel pc o)
          (operandEvalStartCfg
            (R := LoadInstructionTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteEmbedCfg (encodeLoadLabel pc o)
        (embedOperandReturnCfg o.toOp
          (mapLabelCfg (fun l : FullLoadLabel (BoundedPC p) => Sum.inr l)
            (mapLabelCfg (fun l : FullLoadFinishLabel (BoundedPC p) => Sum.inr l)
              (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
                (cleanReturnCfg (nextPC p pc) finalState
                  (operandBoundaryBase w (operandWordValue w o.toOp s.mem)
                    s.mem (coreStacks w s)))))))) := by
  rcases loadInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) (fun _ => .halt) w s.acc s.mem hm
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  refine ⟨steps, hsteps, finalState, ?_⟩
  apply transport_finiteLocal_run
    (encodeLoadLabel pc o) (nextPC p pc)
    (loadInstructionProgram o.toOp (nextPC p pc) (fun _ => .halt))
    (finiteInterpreterProgram p N hbound)
  · intro label
    simp [finiteInterpreterProgram, encodeLoadLabel]
  · exact hrun
  · cases o <;> rfl

theorem finite_load_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (o : BoundedOp N) (w : Nat) (s : SparseState) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= loadInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeLoadLabel pc o)
          (operandEvalStartCfg
            (R := LoadInstructionTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc := operandWordValue w o.toOp s.mem})) := by
  let haltRight : BoundedPC p -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N) := fun _ => .halt
  rcases loadInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc s.mem hm
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (LoadInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N) :=
    embedOperandReturnCfg o.toOp
    (mapLabelCfg (fun l : FullLoadLabel (BoundedPC p) => Sum.inr l)
      (mapLabelCfg (fun l : FullLoadFinishLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
          (cleanReturnCfg (nextPC p pc) finalState
            (operandBoundaryBase w (operandWordValue w o.toOp s.mem)
              s.mem (coreStacks w s))))))
  have hfinal : finalCfg.l.isSome := by
    cases o <;> rfl
  have hhalt :
      loadInstructionProgram o.toOp (nextPC p pc) haltRight
        (finalCfg.l.get hfinal) = .halt := by
    cases o <;> rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch
    (encodeLoadLabel pc o) (nextPC p pc)
    (loadInstructionProgram o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram, encodeLoadLabel, haltRight])
    (d := finalCfg) hrun hfinal hhalt
  have hpres := iterate_preservesDispatch
    (loadInstructionProgram o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      loadInstructionProgram_preservesDispatch (N := N) o.toOp (nextPC p pc))
    _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    cases o <;>
      simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
        lensRenamedCfg, FullInterpreterState.dispatchLens,
        FullInterpreterState.literalLens, FullInterpreterState.macroLens,
        InterpreterMacroState.dispatchLens, StateLens.comp]
        using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg, operandBoundaryBase_coreStacks,
      Function.iterate_succ_apply, embedOperandReturnCfg,
      embedDirectReturnCfg, embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg, embedDirectTailReturnCfg]
      using hglobal

theorem finite_load_instruction {p : Program} {N pc w : Nat}
    (hbound : programArgumentBound p <= N) (o : Op)
    (hfetch : p[pc]? = some (.load o))
    (s : SparseState) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    let harg : operandArgument o <= N :=
      (instrArgument_le_programArgumentBound hfetch).trans hbound
    let bo := BoundedOp.ofOp o harg
    ∃ steps, steps <= loadInstructionBound w s.mem + 3 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc := operandWordValue w o s.mem})) := by
  dsimp only
  let harg : operandArgument o <= N :=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo := BoundedOp.ofOp o harg
  have hfetchStep := finite_step_fetch_data hbound hfetch (by simp) (by simp)
    state (coreStacks w s)
  have hfetchIter :
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[1])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg
        (.control (.data (boundPC p pc) .load)) state (coreStacks w s)) := by
    simpa using hfetchStep
  have hentryStep := finite_step_load_entry hbound (boundPC p pc) o
    (by simpa [fetch_boundPC] using hfetch) state (coreStacks w s)
  have hstartEq :
      finiteEmbedCfg (encodeLoadLabel (boundPC p pc) bo)
        (operandEvalStartCfg
          (R := LoadInstructionTailLabel (BoundedPC p)) bo.toOp
          bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s)) =
      finiteInterpreterCfg
        (encodeLoadLabel (boundPC p pc) bo
          (by simpa [bo] using operandEvalStartLabel o))
        (FullInterpreterState.literalLens.put state
          (BoundedLiteralControl.initial harg)) (coreStacks w s) := by
    rw [operandEvalStartCfg_coreStacks]
    cases o <;> rfl
  have hentryIter :
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[1])
        (some (finiteInterpreterCfg
          (.control (.data (boundPC p pc) .load)) state (coreStacks w s))) =
      some (finiteEmbedCfg (encodeLoadLabel (boundPC p pc) bo)
        (operandEvalStartCfg
          (R := LoadInstructionTailLabel (BoundedPC p)) bo.toOp
          bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))) := by
    rw [hstartEq]
    simpa using hentryStep
  rcases finite_load_to_fetch hbound (boundPC p pc) bo w s hm state with
    ⟨localSteps, hlocalBound, finalState, hdispatch, hlocal⟩
  have hprefix := chain_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step (finiteInterpreterProgram p N hbound)))
    hfetchIter hentryIter
  have hall := chain_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step (finiteInterpreterProgram p N hbound)))
    hprefix hlocal
  refine ⟨2 + localSteps, by omega, finalState, hdispatch, ?_⟩
  simpa [bo] using hall

theorem finite_add_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (o : BoundedOp N) (w : Nat) (s : SparseState) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= addInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeAddLabel pc o)
          (operandEvalStartCfg
            (R := AddInstructionTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc :=
          (s.acc + operandWordValue w o.toOp s.mem) % 2 ^ w})) := by
  let haltRight : BoundedPC p -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N) := fun _ => .halt
  rcases addInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc s.mem hm
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (AddInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N) :=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg (fun l : FullAddPhaseLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
          (cleanReturnCfg (nextPC p pc) finalState
            (operandBoundaryBase w
              ((s.acc + operandWordValue w o.toOp s.mem) % 2 ^ w)
              s.mem (coreStacks w s)))))
  have hfinal : finalCfg.l.isSome := by cases o <;> rfl
  have hhalt : addInstructionProgram o.toOp (nextPC p pc) haltRight
      (finalCfg.l.get hfinal) = .halt := by cases o <;> rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch
    (encodeAddLabel pc o) (nextPC p pc)
    (addInstructionProgram o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram, encodeAddLabel, haltRight])
    (d := finalCfg) hrun hfinal hhalt
  have hpres := iterate_preservesDispatch
    (addInstructionProgram o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      addInstructionProgram_preservesDispatch (N := N) o.toOp (nextPC p pc))
    _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    cases o <;>
      simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
        lensRenamedCfg, FullInterpreterState.dispatchLens,
        FullInterpreterState.literalLens, FullInterpreterState.macroLens,
        InterpreterMacroState.dispatchLens, StateLens.comp] using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg, operandBoundaryBase_coreStacks,
      Function.iterate_succ_apply, embedOperandReturnCfg,
      embedDirectReturnCfg, embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg, embedDirectTailReturnCfg]
      using hglobal

set_option maxHeartbeats 1000000 in
theorem finite_add_instruction {p : Program} {N pc w : Nat}
    (hbound : programArgumentBound p <= N) (o : Op)
    (hfetch : p[pc]? = some (.add o))
    (s : SparseState) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= addInstructionBound w s.mem + 3 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc :=
          (s.acc + sparseValue w o s.mem) % 2 ^ w})) := by
  let harg : operandArgument o <= N :=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo := BoundedOp.ofOp o harg
  let localCfg := finiteEmbedCfg (encodeAddLabel (boundPC p pc) bo)
    (operandEvalStartCfg
      (R := AddInstructionTailLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare := finite_step_prepare_entry hbound (boundPC p pc) (.add o)
    .add (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .add))
        state (coreStacks w s)) = some localCfg := by
    rw [hprepare]
    simp [finitePrepareInstr, finiteInitializeEntry, instrArgument,
      localCfg, operandEvalStartCfg_coreStacks, finiteEmbedCfg,
      mapLabelCfg, finiteInterpreterCfg]
    cases o <;> simp [bo, BoundedOp.ofOp] <;> constructor <;> congr
  rcases finite_add_to_fetch hbound (boundPC p pc) bo w s hm state with
    ⟨localSteps, hlocalBound, finalState, hdispatch, hlocal⟩
  have hall := finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with acc :=
        (s.acc + operandWordValue w bo.toOp s.mem) % 2 ^ w}))
    hentry hlocal
  refine ⟨2 + localSteps, by omega, finalState, hdispatch, ?_⟩
  simpa [bo, sparseValue, operandWordValue] using hall

theorem finite_bitwise_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (kind : BitwiseKind) (o : BoundedOp N) (w : Nat) (s : SparseState)
    (hm : s.mem.Normalized w) (state : FullInterpreterState N) :
    ∃ steps, steps <= zipInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeBitwiseLabel pc kind o)
          (operandEvalStartCfg
            (R := ZipInstructionTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc :=
          (kind.natFn w s.acc (operandWordValue w o.toOp s.mem) % 2 ^ w)})) := by
  let haltRight : BoundedPC p -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N) := fun _ => .halt
  rcases bitwiseInstruction_correct kind o.toOp o.operandArgument_toOp
      w s.acc s.mem hm (nextPC p pc) haltRight
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (ZipInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N) :=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg (fun l : FullZipPhaseLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
          (cleanReturnCfg (nextPC p pc) finalState
            (operandBoundaryBase w
              (kind.natFn w s.acc (operandWordValue w o.toOp s.mem) % 2 ^ w)
              s.mem (coreStacks w s)))))
  have hfinal : finalCfg.l.isSome := by cases o <;> rfl
  have hhalt : bitwiseInstructionProgram kind o.toOp (nextPC p pc) haltRight
      (finalCfg.l.get hfinal) = .halt := by cases o <;> rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch
    (encodeBitwiseLabel pc kind o) (nextPC p pc)
    (bitwiseInstructionProgram kind o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label
        simp [finiteInterpreterProgram, encodeBitwiseLabel, haltRight])
    (d := finalCfg) hrun hfinal hhalt
  have hpres := iterate_preservesDispatch
    (bitwiseInstructionProgram kind o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (bitwiseInstructionProgram_preservesDispatch
        (N := N) kind o.toOp (nextPC p pc))) _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    cases o <;> simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
      lensRenamedCfg, FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens, FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens, StateLens.comp] using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg, operandBoundaryBase_coreStacks,
      Function.iterate_succ_apply, embedOperandReturnCfg,
      embedDirectReturnCfg, embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg, embedDirectTailReturnCfg]
      using hglobal

theorem finite_sub_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (o : BoundedOp N) (w : Nat) (s : SparseState) (hacc : s.acc < 2 ^ w)
    (hm : s.mem.Normalized w) (state : FullInterpreterState N) :
    ∃ steps, steps <= subtractInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeSubLabel pc o)
          (operandEvalStartCfg
            (R := SubtractInstructionTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc := s.acc - sparseValue w o.toOp s.mem})) := by
  let haltRight : BoundedPC p -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N) := fun _ => .halt
  rcases subtractInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc hacc s.mem hm
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (SubtractInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N) :=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg (fun l : FullSubtractLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l : FullSubtractTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l : SubtractInstallPhaseLabel (BoundedPC p) => Sum.inr l)
            (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
              (cleanReturnCfg (nextPC p pc) finalState
                (operandBoundaryBase w (s.acc - sparseValue w o.toOp s.mem)
                  s.mem (coreStacks w s)))))))
  have hfinal : finalCfg.l.isSome := by cases o <;> rfl
  have hhalt : subtractInstructionProgram o.toOp (nextPC p pc) haltRight
      (finalCfg.l.get hfinal) = .halt := by cases o <;> rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch
    (encodeSubLabel pc o) (nextPC p pc)
    (subtractInstructionProgram o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram, encodeSubLabel, haltRight])
    (d := finalCfg) hrun hfinal hhalt
  have hpres := iterate_preservesDispatch
    (subtractInstructionProgram o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (subtractInstructionProgram_preservesDispatch
        (N := N) o.toOp (nextPC p pc))) _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    cases o <;> simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
      lensRenamedCfg, FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens, FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens, StateLens.comp] using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg, operandBoundaryBase_coreStacks,
      Function.iterate_succ_apply, embedOperandReturnCfg,
      embedDirectReturnCfg, embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg, embedDirectTailReturnCfg]
      using hglobal

theorem finite_mul_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (o : BoundedOp N) (w : Nat) (hw : 0 < w) (s : SparseState)
    (hm : s.mem.Normalized w) (state : FullInterpreterState N) :
    ∃ steps, steps <= mulInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeMulLabel pc o)
          (operandEvalStartCfg
            (R := MulInstructionTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc :=
          (s.acc * operandWordValue w o.toOp s.mem) % 2 ^ w})) := by
  let haltRight : BoundedPC p -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N) := fun _ => .halt
  rcases mulInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc hw s.mem hm
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (MulInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N) :=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg (fun l : FullMulLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l : FullMulFinishLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
            (cleanReturnCfg (nextPC p pc) finalState
              (operandBoundaryBase w
                ((s.acc * operandWordValue w o.toOp s.mem) % 2 ^ w)
                s.mem (coreStacks w s))))))
  have hfinal : finalCfg.l.isSome := by cases o <;> rfl
  have hhalt : mulInstructionProgram o.toOp (nextPC p pc) haltRight
      (finalCfg.l.get hfinal) = .halt := by cases o <;> rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch
    (encodeMulLabel pc o) (nextPC p pc)
    (mulInstructionProgram o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram, encodeMulLabel, haltRight])
    (d := finalCfg) hrun hfinal hhalt
  have hpres := iterate_preservesDispatch
    (mulInstructionProgram o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (mulInstructionProgram_preservesDispatch
        (N := N) o.toOp (nextPC p pc))) _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    cases o <;> simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
      lensRenamedCfg, FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens, FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens, StateLens.comp] using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg, operandBoundaryBase_coreStacks,
      Function.iterate_succ_apply, embedOperandReturnCfg,
      embedDirectReturnCfg, embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg, embedDirectTailReturnCfg]
      using hglobal

set_option maxHeartbeats 5000000 in
theorem finite_div_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (o : BoundedOp N) (w : Nat) (s : SparseState) (hacc : s.acc < 2 ^ w)
    (hm : s.mem.Normalized w) (state : FullInterpreterState N) :
    ∃ steps, steps <= divideInstructionTotalBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeDivLabel pc o)
          (operandEvalStartCfg
            (R := FullDividePostLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc := s.acc / sparseValue w o.toOp s.mem})) := by
  let haltRight : BoundedPC p -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N) := fun _ => .halt
  rcases divideInstructionTotal_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc hacc s.mem hm
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (DivideInstructionTotalLabel o.toOp (BoundedPC p))
      (FullInterpreterState N) :=
    embedOperandReturnCfg o.toOp
      (embedFullDivideReturnCfg
        (mapLabelCfg (fun l : ConditionalZeroTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
            (cleanReturnCfg (nextPC p pc) finalState
              (operandBoundaryBase w (s.acc / sparseValue w o.toOp s.mem)
                s.mem (coreStacks w s))))))
  have hfinal : finalCfg.l.isSome := by cases o <;> rfl
  have hhalt : divideInstructionTotalProgram o.toOp (nextPC p pc) haltRight
      (finalCfg.l.get hfinal) = .halt := by cases o <;> rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch
    (encodeDivLabel pc o) (nextPC p pc)
    (divideInstructionTotalProgram o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram, encodeDivLabel, haltRight])
    (d := finalCfg) hrun hfinal hhalt
  have hpres := iterate_preservesDispatch
    (divideInstructionTotalProgram o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (divideInstructionProgram_preservesDispatch
        (N := N) o.toOp (nextPC p pc))) _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    cases o <;> simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
      lensRenamedCfg, FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens, FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens, StateLens.comp] using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg, operandBoundaryBase_coreStacks,
      Function.iterate_succ_apply, embedOperandReturnCfg,
      embedDirectReturnCfg, embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg, embedDirectTailReturnCfg,
      embedFullDivideReturnCfg]
      using hglobal

set_option maxHeartbeats 1000000 in
theorem finite_shiftLeft_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (o : BoundedOp N) (w : Nat) (hw : 0 < w) (s : SparseState)
    (hacc : s.acc < 2 ^ w) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= shiftInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeShiftLabel pc false o)
          (operandEvalStartCfg
            (R := FullShiftLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc :=
          (s.acc * 2 ^ sparseValue w o.toOp s.mem) % 2 ^ w})) := by
  let haltRight : BoundedPC p -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N) := fun _ => .halt
  rcases shiftLeftInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc hw hacc s.mem hm
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (ShiftInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N) :=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg Sum.inr
        (mapLabelCfg (fun l : ConditionalZeroTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
            (cleanReturnCfg (nextPC p pc) finalState
              (operandBoundaryBase w
                (s.acc * 2 ^ sparseValue w o.toOp s.mem % 2 ^ w)
                s.mem (coreStacks w s))))))
  have hfinal : finalCfg.l.isSome := by cases o <;> rfl
  have hhalt : shiftInstructionProgram o.toOp false (nextPC p pc) haltRight
      (finalCfg.l.get hfinal) = .halt := by cases o <;> rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch
    (encodeShiftLabel pc false o) (nextPC p pc)
    (shiftInstructionProgram o.toOp false (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label
        simp [finiteInterpreterProgram, encodeShiftLabel, haltRight])
    (d := finalCfg) hrun hfinal hhalt
  have hpres := iterate_preservesDispatch
    (shiftInstructionProgram o.toOp false (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (shiftInstructionProgram_preservesDispatch
        (N := N) false o.toOp (nextPC p pc))) _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    cases o <;> simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
      lensRenamedCfg, FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens, FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens, StateLens.comp] using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg, operandBoundaryBase_coreStacks,
      Function.iterate_succ_apply, embedOperandReturnCfg,
      embedDirectReturnCfg, embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg, embedDirectTailReturnCfg]
      using hglobal

set_option maxHeartbeats 1000000 in
theorem finite_shiftRight_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (o : BoundedOp N) (w : Nat) (hw : 0 < w) (s : SparseState)
    (hacc : s.acc < 2 ^ w) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= shiftInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeShiftLabel pc true o)
          (operandEvalStartCfg
            (R := FullShiftLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc :=
          (s.acc / 2 ^ sparseValue w o.toOp s.mem) % 2 ^ w})) := by
  let haltRight : BoundedPC p -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N) := fun _ => .halt
  rcases shiftRightInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc hw hacc s.mem hm
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (ShiftInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N) :=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg Sum.inr
        (mapLabelCfg (fun l : ConditionalZeroTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
            (cleanReturnCfg (nextPC p pc) finalState
              (operandBoundaryBase w
                (s.acc / 2 ^ sparseValue w o.toOp s.mem % 2 ^ w)
                s.mem (coreStacks w s))))))
  have hfinal : finalCfg.l.isSome := by cases o <;> rfl
  have hhalt : shiftInstructionProgram o.toOp true (nextPC p pc) haltRight
      (finalCfg.l.get hfinal) = .halt := by cases o <;> rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch
    (encodeShiftLabel pc true o) (nextPC p pc)
    (shiftInstructionProgram o.toOp true (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label
        simp [finiteInterpreterProgram, encodeShiftLabel, haltRight])
    (d := finalCfg) hrun hfinal hhalt
  have hpres := iterate_preservesDispatch
    (shiftInstructionProgram o.toOp true (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (shiftInstructionProgram_preservesDispatch
        (N := N) true o.toOp (nextPC p pc))) _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    cases o <;> simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
      lensRenamedCfg, FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens, FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens, StateLens.comp] using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg, operandBoundaryBase_coreStacks,
      Function.iterate_succ_apply, embedOperandReturnCfg,
      embedDirectReturnCfg, embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg, embedDirectTailReturnCfg]
      using hglobal

set_option maxHeartbeats 1000000 in
theorem finite_write_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (o : BoundedOp N) (w : Nat) (s : SparseState) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= writeInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeWriteLabel pc o)
          (operandEvalStartCfg
            (R := WriteTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with out :=
          s.out ++ [operandWordValue w o.toOp s.mem]})) := by
  let haltRight : BoundedPC p -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N) := fun _ => .halt
  rcases writeInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc s.mem hm
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (WriteInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N) :=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg (fun l : WriteMove1Label (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l : WriteMove2Label (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l : WriteAfterLabel (BoundedPC p) => Sum.inr l)
            (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
              (cleanReturnCfg (nextPC p pc) finalState
                (writeResultBase w s.acc (operandWordValue w o.toOp s.mem)
                  s.mem (coreStacks w s)))))))
  have hfinal : finalCfg.l.isSome := by cases o <;> rfl
  have hhalt : writeInstructionProgram o.toOp (nextPC p pc) haltRight
      (finalCfg.l.get hfinal) = .halt := by cases o <;> rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch
    (encodeWriteLabel pc o) (nextPC p pc)
    (writeInstructionProgram o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram, encodeWriteLabel, haltRight])
    (d := finalCfg) hrun hfinal hhalt
  have hpres := iterate_preservesDispatch
    (writeInstructionProgram o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (writeInstructionProgram_preservesDispatch
        (N := N) o.toOp (nextPC p pc))) _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    cases o <;> simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
      lensRenamedCfg, FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens, FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens, StateLens.comp] using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg, writeResultBase_coreStacks,
      Function.iterate_succ_apply, embedOperandReturnCfg,
      embedDirectReturnCfg, embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg, embedDirectTailReturnCfg]
      using hglobal

set_option maxHeartbeats 1000000 in
theorem finite_store_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (address : Fin (N + 1)) (w : Nat) (s : SparseState)
    (hm : s.mem.Normalized w) (state : FullInterpreterState N) :
    ∃ steps, steps <= storeInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeStoreLabel pc address)
          (operandEvalStartCfg
            (R := StoreInstructionTailLabel (BoundedPC p)) (.lit address.val)
            (Nat.le_of_lt_succ address.isLt) w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with mem :=
          (s.mem.write w address.val s.acc)})) := by
  let haltRight : BoundedPC p -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N) := fun _ => .halt
  have haddress : address.val <= N := by omega
  rcases storeInstruction_correct address.val haddress
      (nextPC p pc) haltRight w s.acc s.mem hm
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (StoreInstructionLabel address.val (BoundedPC p))
      (FullInterpreterState N) :=
    embedOperandReturnCfg (.lit address.val)
      (mapLabelCfg (fun l : FullStoreLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l : StorePrependTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l : FullPrependLabel (BoundedPC p) => Sum.inr l)
            (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
              (cleanReturnCfg (nextPC p pc) finalState
                (operandBoundaryBase w s.acc
                  (s.mem.write w address.val s.acc) (coreStacks w s)))))))
  have hfinal : finalCfg.l.isSome := by rfl
  have hhalt : storeInstructionProgram address.val (nextPC p pc) haltRight
      (finalCfg.l.get hfinal) = .halt := by rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch
    (encodeStoreLabel pc address) (nextPC p pc)
    (storeInstructionProgram address.val (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram, encodeStoreLabel, haltRight])
    (d := finalCfg) hrun hfinal hhalt
  have hpres := iterate_preservesDispatch
    (storeInstructionProgram address.val (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (storeInstructionProgram_preservesDispatch
        (N := N) address.val (nextPC p pc))) _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
      lensRenamedCfg, FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens, FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens, StateLens.comp] using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  simpa [finalCfg, operandBoundaryBase_coreStacks_withMemory,
    Function.iterate_succ_apply, embedOperandReturnCfg]
    using hglobal

set_option maxHeartbeats 1000000 in
theorem finite_storeInd_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (address : Fin (N + 1)) (w : Nat) (s : SparseState)
    (hm : s.mem.Normalized w) (state : FullInterpreterState N) :
    ∃ steps, steps <= storeIndInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeStoreIndLabel pc address)
          (operandEvalStartCfg
            (R := StoreInstructionTailLabel (BoundedPC p)) (.mem address.val)
            (Nat.le_of_lt_succ address.isLt) w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with mem := (s.mem.write w
          (s.mem.read (address.val % 2 ^ w)) s.acc)})) := by
  let haltRight : BoundedPC p -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N) := fun _ => .halt
  have haddress : address.val <= N := by omega
  rcases storeIndInstruction_correct address.val haddress
      (nextPC p pc) haltRight w s.acc s.mem hm
      (coreStacks w s) state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (StoreIndInstructionLabel address.val (BoundedPC p))
      (FullInterpreterState N) :=
    embedOperandReturnCfg (.mem address.val)
      (mapLabelCfg (fun l : FullStoreLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l : StorePrependTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l : FullPrependLabel (BoundedPC p) => Sum.inr l)
            (mapLabelCfg (fun l : BoundedPC p => Sum.inr l)
              (cleanReturnCfg (nextPC p pc) finalState
                (operandBoundaryBase w s.acc
                  (s.mem.write w (s.mem.read (address.val % 2 ^ w)) s.acc)
                  (coreStacks w s)))))))
  have hfinal : finalCfg.l.isSome := by rfl
  have hhalt : storeIndInstructionProgram address.val (nextPC p pc) haltRight
      (finalCfg.l.get hfinal) = .halt := by rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch
    (encodeStoreIndLabel pc address) (nextPC p pc)
    (storeIndInstructionProgram address.val (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label
        simp [finiteInterpreterProgram, encodeStoreIndLabel, haltRight])
    (d := finalCfg) hrun hfinal hhalt
  have hpres := iterate_preservesDispatch
    (storeIndInstructionProgram address.val (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (storeIndInstructionProgram_preservesDispatch
        (N := N) address.val (nextPC p pc))) _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
      lensRenamedCfg, FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens, FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens, StateLens.comp] using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  simpa [finalCfg, operandBoundaryBase_coreStacks_withMemory,
    Function.iterate_succ_apply, embedOperandReturnCfg,
    embedDirectReturnCfg]
    using hglobal

set_option maxHeartbeats 1000000 in
theorem finite_read_to_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (address : Fin (N + 1)) (w value : Nat) (inputTail : List Nat)
    (s : SparseState) (hinp : s.inp = value :: inputTail)
    (hm : s.mem.Normalized w) (state : FullInterpreterState N) :
    ∃ steps, steps <= readInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeReadLabel pc address)
          (operandEvalStartCfg
            (R := ReadTailLabel (Sum (BoundedPC p) Unit)) (.lit address.val)
            (Nat.le_of_lt_succ address.isLt) w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with
          mem := s.mem.write w address.val value,
          inp := inputTail})) := by
  let R := Sum (BoundedPC p) Unit
  let haltRight : R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N) := fun _ => .halt
  have haddress : address.val <= N := by omega
  have hinput : (coreStacks w s) .input =
      encodeFixedWord w value ++ encodeInputStack w inputTail := by
    simp [coreStacks, encodeInputStack, encodeWordList, hinp,
      encodeFixedWord, List.append_assoc]
  rcases readInstruction_correct address.val haddress
      (Sum.inr ()) (Sum.inl (nextPC p pc)) haltRight
      w s.acc value (encodeInputStack w inputTail)
      s.mem hm (coreStacks w s) hinput state with
    ⟨steps, hsteps, finalState, hrun⟩
  let finalCfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (ReadInstructionLabel address.val R)
      (FullInterpreterState N) :=
    embedOperandReturnCfg (.lit address.val)
      (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr
        (cleanReturnCfg (Sum.inl (nextPC p pc)) finalState
          (prependResultStacks w address.val value s.mem
            (readTransferStacks (encodeInputStack w inputTail)
              ((fixedBits w value).reverse.map SparseSymbol.bit)
              (operandResultBase w s.acc
                (operandWordValue w (.lit address.val) s.mem)
                s.mem (coreStacks w s)))))))
  have hfinal : finalCfg.l.isSome := by rfl
  have hhalt : readInstructionProgram address.val (Sum.inr ())
      (Sum.inl (nextPC p pc)) haltRight
      (finalCfg.l.get hfinal) = .halt := by rfl
  have hglobal := transport_finiteLocal_cfg_to_fetch_selective
    (encodeReadLabel pc address) (nextPC p pc)
    (readInstructionProgram address.val (Sum.inr ()) (Sum.inl (nextPC p pc)) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by
      intro label hn
      cases label with
      | inl l =>
          simpa [finiteInterpreterProgram, encodeReadLabel] using
            (wrapFiniteLocal_encode_nonhalt (encodeReadLabel pc address)
              (nextPC p pc)
              (readInstructionProgram address.val (Sum.inr ())
                (Sum.inl (nextPC p pc)) haltRight) (Sum.inl l) hn)
      | inr l =>
          cases l with
          | inl l =>
              simpa [finiteInterpreterProgram, encodeReadLabel] using
                (wrapFiniteLocal_encode_nonhalt (encodeReadLabel pc address)
                  (nextPC p pc)
                  (readInstructionProgram address.val (Sum.inr ())
                    (Sum.inl (nextPC p pc)) haltRight)
                  (Sum.inr (Sum.inl l)) hn)
          | inr l =>
              cases l with
              | inl l =>
                  simpa [finiteInterpreterProgram, encodeReadLabel] using
                    (wrapFiniteLocal_encode_nonhalt (encodeReadLabel pc address)
                      (nextPC p pc)
                      (readInstructionProgram address.val (Sum.inr ())
                        (Sum.inl (nextPC p pc)) haltRight)
                      (Sum.inr (Sum.inr (Sum.inl l))) hn)
              | inr l =>
                  cases l with
                  | inl returnPC =>
                      simpa [finiteInterpreterProgram, encodeReadLabel] using
                        (wrapFiniteLocal_encode_nonhalt (encodeReadLabel pc address)
                          (nextPC p pc)
                          (readInstructionProgram address.val (Sum.inr ())
                            (Sum.inl (nextPC p pc)) haltRight)
                          (Sum.inr (Sum.inr (Sum.inr (Sum.inl returnPC)))) hn)
                  | inr u =>
                      cases u
                      exact False.elim (hn rfl))
    (d := finalCfg) hrun hfinal hhalt
    (by
      have hlabel : finalCfg.l.get hfinal =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (nextPC p pc)))) := by rfl
      rw [hlabel]
      simp [finiteInterpreterProgram, encodeReadLabel, wrapFiniteLocal,
        readInstructionProgram, haltRight, stmtIsHalt]
      intro hnonhalt
      change stmtIsHalt
        (readInstructionProgram address.val (Sum.inr ())
          (Sum.inl (nextPC p pc)) haltRight
          (finalCfg.l.get hfinal)) = false at hnonhalt
      rw [hhalt] at hnonhalt
      simp [stmtIsHalt] at hnonhalt)
  have hpres := iterate_preservesDispatch
    (readInstructionProgram address.val (Sum.inr ()) (Sum.inl (nextPC p pc)) haltRight)
    (by simpa [haltRight] using
      (readInstructionProgram_preservesDispatch
        (N := N) address.val (Sum.inr ()) (Sum.inl (nextPC p pc)))) _ finalCfg hrun
  have hdispatch : FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state := by
    simpa [finalCfg, operandEvalStartCfg, literalOperandStartCfg,
      lensRenamedCfg, FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens, FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens, StateLens.comp] using hpres
  refine ⟨steps + 1, by omega, finalState, hdispatch, ?_⟩
  convert hglobal using 1 <;>
    simp [finalCfg, Function.iterate_succ_apply, embedOperandReturnCfg, cleanReturnCfg,
      operandWordValue, sparseValue, Op.value, readResultStacks_coreStacks]
  exact congrArg
    (finiteInterpreterCfg (FiniteInterpreterLabel.fetch (nextPC p pc)) finalState)
    (by simpa [List.map_reverse] using
      (readResultStacks_coreStacks w address.val value s inputTail).symm)

set_option maxHeartbeats 1000000 in
theorem finite_write_instruction {p : Program} {N pc w : Nat}
    (hbound : programArgumentBound p <= N) (o : Op)
    (hfetch : p[pc]? = some (.write o))
    (s : SparseState) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= writeInstructionBound w s.mem + 3 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with out :=
          s.out ++ [sparseValue w o s.mem % 2 ^ w]})) := by
  let harg : operandArgument o <= N :=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo := BoundedOp.ofOp o harg
  let localCfg := finiteEmbedCfg (encodeWriteLabel (boundPC p pc) bo)
    (operandEvalStartCfg
      (R := WriteTailLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare := finite_step_prepare_entry hbound (boundPC p pc) (.write o)
    .write (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .write))
        state (coreStacks w s)) = some localCfg := by
    rw [hprepare]
    simp [finitePrepareInstr, finiteInitializeEntry, instrArgument,
      localCfg, operandEvalStartCfg_coreStacks, finiteEmbedCfg,
      mapLabelCfg, finiteInterpreterCfg]
    cases o <;> simp [bo, BoundedOp.ofOp] <;> constructor <;> congr
  rcases finite_write_to_fetch hbound (boundPC p pc) bo w s hm state with
    ⟨localSteps, hlocalBound, finalState, hdispatch, hlocal⟩
  have hall := finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with out :=
        s.out ++ [operandWordValue w bo.toOp s.mem]}))
    hentry hlocal
  refine ⟨2 + localSteps, by omega, finalState, hdispatch, ?_⟩
  simpa [bo, operandWordValue] using hall

set_option maxHeartbeats 1000000 in
theorem finite_mul_instruction {p : Program} {N pc w : Nat}
    (hbound : programArgumentBound p <= N) (o : Op)
    (hfetch : p[pc]? = some (.mul o)) (hw : 0 < w)
    (s : SparseState) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= mulInstructionBound w s.mem + 3 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc :=
          (s.acc * sparseValue w o s.mem) % 2 ^ w})) := by
  let harg : operandArgument o <= N :=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo := BoundedOp.ofOp o harg
  let localCfg := finiteEmbedCfg (encodeMulLabel (boundPC p pc) bo)
    (operandEvalStartCfg
      (R := MulInstructionTailLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare := finite_step_prepare_entry hbound (boundPC p pc) (.mul o)
    .mul (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .mul))
        state (coreStacks w s)) = some localCfg := by
    rw [hprepare]
    simp [finitePrepareInstr, finiteInitializeEntry, instrArgument,
      localCfg, operandEvalStartCfg_coreStacks, finiteEmbedCfg,
      mapLabelCfg, finiteInterpreterCfg]
    cases o <;> simp [bo, BoundedOp.ofOp] <;> constructor <;> congr
  rcases finite_mul_to_fetch hbound (boundPC p pc) bo w hw s hm state with
    ⟨localSteps, hlocalBound, finalState, hdispatch, hlocal⟩
  have hall := finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with acc :=
        (s.acc * operandWordValue w bo.toOp s.mem) % 2 ^ w}))
    hentry hlocal
  refine ⟨2 + localSteps, by omega, finalState, hdispatch, ?_⟩
  simpa [bo, operandWordValue] using hall

set_option maxHeartbeats 1500000 in
theorem finite_div_instruction {p : Program} {N pc w : Nat}
    (hbound : programArgumentBound p <= N) (o : Op)
    (hfetch : p[pc]? = some (.div o)) (s : SparseState)
    (hacc : s.acc < 2 ^ w) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= divideInstructionTotalBound w s.mem + 3 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc :=
          (s.acc / sparseValue w o s.mem) % 2 ^ w})) := by
  let harg : operandArgument o <= N :=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo := BoundedOp.ofOp o harg
  let localCfg := finiteEmbedCfg (encodeDivLabel (boundPC p pc) bo)
    (operandEvalStartCfg
      (R := FullDividePostLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare := finite_step_prepare_entry hbound (boundPC p pc) (.div o)
    .div (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .div))
        state (coreStacks w s)) = some localCfg := by
    rw [hprepare]
    simp [finitePrepareInstr, finiteInitializeEntry, instrArgument,
      localCfg, operandEvalStartCfg_coreStacks, finiteEmbedCfg,
      mapLabelCfg, finiteInterpreterCfg]
    cases o <;> simp [bo, BoundedOp.ofOp] <;> constructor <;> congr
  rcases finite_div_to_fetch hbound (boundPC p pc) bo w s hacc hm state with
    ⟨localSteps, hlocalBound, finalState, hdispatch, hlocal⟩
  have hall := finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with acc := s.acc / sparseValue w bo.toOp s.mem}))
    hentry hlocal
  refine ⟨2 + localSteps, by omega, finalState, hdispatch, ?_⟩
  have hlt : s.acc / sparseValue w o s.mem < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hacc
  simpa [bo, Nat.mod_eq_of_lt hlt] using hall

set_option maxHeartbeats 1200000 in
theorem finite_sub_instruction {p : Program} {N pc w : Nat}
    (hbound : programArgumentBound p <= N) (o : Op)
    (hfetch : p[pc]? = some (.sub o)) (s : SparseState)
    (hacc : s.acc < 2 ^ w) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= subtractInstructionBound w s.mem + 3 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc :=
          (s.acc - sparseValue w o s.mem) % 2 ^ w})) := by
  let harg : operandArgument o <= N :=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo := BoundedOp.ofOp o harg
  let localCfg := finiteEmbedCfg (encodeSubLabel (boundPC p pc) bo)
    (operandEvalStartCfg
      (R := SubtractInstructionTailLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare := finite_step_prepare_entry hbound (boundPC p pc) (.sub o)
    .sub (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .sub))
        state (coreStacks w s)) = some localCfg := by
    rw [hprepare]
    simp [finitePrepareInstr, finiteInitializeEntry, instrArgument,
      localCfg, operandEvalStartCfg_coreStacks, finiteEmbedCfg,
      mapLabelCfg, finiteInterpreterCfg]
    cases o <;> simp [bo, BoundedOp.ofOp] <;> constructor <;> congr
  rcases finite_sub_to_fetch hbound (boundPC p pc) bo w s hacc hm state with
    ⟨localSteps, hlocalBound, finalState, hdispatch, hlocal⟩
  have hall := finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with acc := s.acc - sparseValue w bo.toOp s.mem}))
    hentry hlocal
  refine ⟨2 + localSteps, by omega, finalState, hdispatch, ?_⟩
  have hlt : s.acc - sparseValue w o s.mem < 2 ^ w :=
    lt_of_le_of_lt (Nat.sub_le _ _) hacc
  simpa [bo, Nat.mod_eq_of_lt hlt] using hall

set_option maxHeartbeats 1000000 in
theorem finite_store_instruction {p : Program} {N pc w : Nat}
    (hbound : programArgumentBound p <= N) (address : Nat)
    (hfetch : p[pc]? = some (.store address)) (s : SparseState)
    (hm : s.mem.Normalized w) (state : FullInterpreterState N) :
    ∃ steps, steps <= storeInstructionBound w s.mem + 3 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with mem := (s.mem.write w address s.acc)})) := by
  let harg : address <= N :=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let ba := boundedAddress address harg
  let localCfg := finiteEmbedCfg (encodeStoreLabel (boundPC p pc) ba)
    (operandEvalStartCfg
      (R := StoreInstructionTailLabel (BoundedPC p)) (.lit ba.val)
      (Nat.le_of_lt_succ ba.isLt) w s.acc s.mem state (coreStacks w s))
  have hprepare := finite_step_prepare_entry hbound (boundPC p pc)
    (.store address) .store (by simpa [fetch_boundPC] using hfetch) rfl
    state (coreStacks w s)
  have hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .store))
        state (coreStacks w s)) = some localCfg := by
    rw [hprepare]
    simp [finitePrepareInstr, finiteInitializeEntry, instrArgument,
      localCfg, operandEvalStartCfg_coreStacks, finiteEmbedCfg,
      mapLabelCfg, finiteInterpreterCfg, ba, harg, boundedAddress] <;>
      constructor <;> congr
  rcases finite_store_to_fetch hbound (boundPC p pc) ba w s hm state with
    ⟨localSteps, hlocalBound, finalState, hdispatch, hlocal⟩
  have hall := finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with mem := s.mem.write w ba.val s.acc}))
    hentry hlocal
  refine ⟨2 + localSteps, by omega, finalState, hdispatch, ?_⟩
  simpa [ba, boundedAddress] using hall

set_option maxHeartbeats 1000000 in
theorem finite_storeInd_instruction {p : Program} {N pc w : Nat}
    (hbound : programArgumentBound p <= N) (address : Nat)
    (hfetch : p[pc]? = some (.storeInd address)) (s : SparseState)
    (hm : s.mem.Normalized w) (state : FullInterpreterState N) :
    ∃ steps, steps <= storeIndInstructionBound w s.mem + 3 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with mem := (s.mem.write w
          (s.mem.read (address % 2 ^ w)) s.acc)})) := by
  let harg : address <= N :=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let ba := boundedAddress address harg
  let localCfg := finiteEmbedCfg (encodeStoreIndLabel (boundPC p pc) ba)
    (operandEvalStartCfg
      (R := StoreInstructionTailLabel (BoundedPC p)) (.mem ba.val)
      (Nat.le_of_lt_succ ba.isLt) w s.acc s.mem state (coreStacks w s))
  have hprepare := finite_step_prepare_entry hbound (boundPC p pc)
    (.storeInd address) .storeInd (by simpa [fetch_boundPC] using hfetch) rfl
    state (coreStacks w s)
  have hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .storeInd))
        state (coreStacks w s)) = some localCfg := by
    rw [hprepare]
    simp [finitePrepareInstr, finiteInitializeEntry, instrArgument,
      localCfg, operandEvalStartCfg_coreStacks, finiteEmbedCfg,
      mapLabelCfg, finiteInterpreterCfg, ba, harg, boundedAddress] <;>
      constructor <;> congr
  rcases finite_storeInd_to_fetch hbound (boundPC p pc) ba w s hm state with
    ⟨localSteps, hlocalBound, finalState, hdispatch, hlocal⟩
  have hall := finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with mem := (s.mem.write w
        (s.mem.read (ba.val % 2 ^ w)) s.acc)}))
    hentry hlocal
  refine ⟨2 + localSteps, by omega, finalState, hdispatch, ?_⟩
  simpa [ba, boundedAddress] using hall

set_option maxHeartbeats 1200000 in
theorem finite_read_instruction {p : Program} {N pc w : Nat}
    (hbound : programArgumentBound p <= N) (address value : Nat)
    (inputTail : List Nat) (hfetch : p[pc]? = some (.read address))
    (s : SparseState) (hinp : s.inp = value :: inputTail)
    (hm : s.mem.Normalized w) (state : FullInterpreterState N) :
    ∃ steps, steps <= readInstructionBound w s.mem + 3 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with
          mem := s.mem.write w address value,
          inp := inputTail})) := by
  let harg : address <= N :=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let ba := boundedAddress address harg
  let localCfg := finiteEmbedCfg (encodeReadLabel (boundPC p pc) ba)
    (operandEvalStartCfg
      (R := ReadTailLabel (Sum (BoundedPC p) Unit)) (.lit ba.val)
      (Nat.le_of_lt_succ ba.isLt) w s.acc s.mem state (coreStacks w s))
  have hprepare := finite_step_prepare_entry hbound (boundPC p pc)
    (.read address) .read (by simpa [fetch_boundPC] using hfetch) rfl
    state (coreStacks w s)
  have hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .read))
        state (coreStacks w s)) = some localCfg := by
    rw [hprepare]
    simp [finitePrepareInstr, finiteInitializeEntry, instrArgument,
      localCfg, operandEvalStartCfg_coreStacks, finiteEmbedCfg,
      mapLabelCfg, finiteInterpreterCfg, ba, harg, boundedAddress] <;>
      constructor <;> congr
  rcases finite_read_to_fetch hbound (boundPC p pc) ba w value inputTail
      s hinp hm state with
    ⟨localSteps, hlocalBound, finalState, hdispatch, hlocal⟩
  have hall := finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with
        mem := s.mem.write w ba.val value,
        inp := inputTail}))
    hentry hlocal
  refine ⟨2 + localSteps, by omega, finalState, hdispatch, ?_⟩
  simpa [ba, boundedAddress] using hall

theorem finite_read_exhausted {p : Program} {N pc w address : Nat}
    (hbound : programArgumentBound p <= N)
    (hfetch : p[pc]? = some (.read address))
    (s : SparseState) (hinp : s.inp = []) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= operandEvalBound w s.mem + 4 ∧
      ∃ finalState finalTapes,
        finalTapes .output = (coreStacks w s) .output ∧
        ((fun x => x.bind (TM2.step
          (finiteInterpreterProgram p N hbound)))^[steps])
          (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
            (coreStacks w s))) =
        some (finiteInterpreterCfg (.control .stopped) finalState finalTapes) := by
  let harg : address <= N :=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let ba := boundedAddress address harg
  let R := Sum (BoundedPC p) Unit
  let haltRight : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N) := fun _ => .halt
  let localCfg := finiteEmbedCfg (encodeReadLabel (boundPC p pc) ba)
    (operandEvalStartCfg
      (R := ReadTailLabel R) (.lit ba.val)
      (Nat.le_of_lt_succ ba.isLt) w s.acc s.mem state (coreStacks w s))
  have hprepare := finite_step_prepare_entry hbound (boundPC p pc)
    (.read address) .read (by simpa [fetch_boundPC] using hfetch) rfl
    state (coreStacks w s)
  have hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .read))
        state (coreStacks w s)) = some localCfg := by
    rw [hprepare]
    simp [finitePrepareInstr, finiteInitializeEntry, instrArgument,
      localCfg, operandEvalStartCfg_coreStacks, finiteEmbedCfg,
      mapLabelCfg, finiteInterpreterCfg, ba, harg, boundedAddress] <;>
      constructor <;> congr
  have hinput : (coreStacks w s) .input = [.inputEnd] := by
    simp [coreStacks, encodeInputStack, encodeWordList, hinp]
  rcases readInstruction_exhausted ba.val (by omega)
      (Sum.inr ()) (Sum.inl (nextPC p (boundPC p pc))) haltRight
      w s.acc s.mem hm (coreStacks w s) hinput state with
    ⟨localSteps, hlocalSteps, finalState, hlocal⟩
  let finalTapes := readTransferStacks [] []
    (operandResultBase w s.acc
      (operandWordValue w (.lit ba.val) s.mem) s.mem (coreStacks w s))
  let finalLocal : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (ReadInstructionLabel ba.val R) (FullInterpreterState N) :=
    embedOperandReturnCfg (.lit ba.val)
      ⟨some (Sum.inr (Sum.inr (.inr ()))), finalState, finalTapes⟩
  have hlocal' :
      ((fun x => x.bind (TM2.step
        (readInstructionProgram ba.val (Sum.inr ())
          (Sum.inl (nextPC p (boundPC p pc))) haltRight)))^[localSteps])
        (some (operandEvalStartCfg
          (R := ReadTailLabel R) (.lit ba.val) (Nat.le_of_lt_succ ba.isLt)
          w s.acc s.mem state (coreStacks w s))) = some finalLocal := by
    simpa [finalLocal, finalTapes] using hlocal
  have hglobal := iterate_mapLabelProgram_until_exit
    (readInstructionProgram ba.val (Sum.inr ())
      (Sum.inl (nextPC p (boundPC p pc))) haltRight)
    (finiteInterpreterProgram p N hbound)
    (encodeReadLabel (boundPC p pc) ba)
    (by
      intro label hnonhalt
      cases label with
      | inl l =>
          simpa [finiteInterpreterProgram, encodeReadLabel] using
            (wrapFiniteLocal_encode_nonhalt
              (encodeReadLabel (boundPC p pc) ba)
              (nextPC p (boundPC p pc))
              (readInstructionProgram ba.val (Sum.inr ())
                (Sum.inl (nextPC p (boundPC p pc))) haltRight)
              (Sum.inl l) hnonhalt)
      | inr l =>
          cases l with
          | inl l =>
              simpa [finiteInterpreterProgram, encodeReadLabel] using
                (wrapFiniteLocal_encode_nonhalt
                  (encodeReadLabel (boundPC p pc) ba)
                  (nextPC p (boundPC p pc))
                  (readInstructionProgram ba.val (Sum.inr ())
                    (Sum.inl (nextPC p (boundPC p pc))) haltRight)
                  (Sum.inr (Sum.inl l)) hnonhalt)
          | inr l =>
              cases l with
              | inl l =>
                  simpa [finiteInterpreterProgram, encodeReadLabel] using
                    (wrapFiniteLocal_encode_nonhalt
                      (encodeReadLabel (boundPC p pc) ba)
                      (nextPC p (boundPC p pc))
                      (readInstructionProgram ba.val (Sum.inr ())
                        (Sum.inl (nextPC p (boundPC p pc))) haltRight)
                      (Sum.inr (Sum.inr (Sum.inl l))) hnonhalt)
              | inr l =>
                  cases l with
                  | inl returnPC =>
                      simpa [finiteInterpreterProgram, encodeReadLabel] using
                        (wrapFiniteLocal_encode_nonhalt
                          (encodeReadLabel (boundPC p pc) ba)
                          (nextPC p (boundPC p pc))
                          (readInstructionProgram ba.val (Sum.inr ())
                            (Sum.inl (nextPC p (boundPC p pc))) haltRight)
                          (Sum.inr (Sum.inr (Sum.inr (Sum.inl returnPC)))) hnonhalt)
                  | inr u =>
                      cases u
                      exact False.elim (hnonhalt rfl))
    hlocal' (by rfl)
  have hglobal' :
      ((fun x => x.bind (TM2.step
        (finiteInterpreterProgram p N hbound)))^[localSteps])
        (some localCfg) =
      some (finiteInterpreterCfg (.control .stopped) finalState finalTapes) := by
    simpa [localCfg, finalLocal, finalTapes, finiteEmbedCfg, mapLabelCfg,
      encodeReadLabel, finiteInterpreterCfg] using hglobal
  have hall := finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.control .stopped) finalState finalTapes)
    hentry hglobal'
  refine ⟨2 + localSteps, by omega, finalState, finalTapes, ?_, ?_⟩
  · simp [finalTapes, readTransferStacks, operandResultBase]
  · exact hall

def bitwiseInstr : BitwiseKind -> Op -> Instr
  | .and => .and
  | .or => .or
  | .xor => .xor
  | .compl => .compl

set_option maxHeartbeats 1500000 in
theorem finite_bitwise_instruction {p : Program} {N pc w : Nat}
    (hbound : programArgumentBound p <= N) (kind : BitwiseKind) (o : Op)
    (hfetch : p[pc]? = some (bitwiseInstr kind o))
    (s : SparseState) (hm : s.mem.Normalized w)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= zipInstructionBound w s.mem + 3 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc :=
          (kind.natFn w s.acc (sparseValue w o s.mem) % 2 ^ w)})) := by
  have hargument : instrArgument (bitwiseInstr kind o) = operandArgument o := by
    cases kind <;> rfl
  let harg : operandArgument o <= N := by
    rw [← hargument]
    exact (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo := BoundedOp.ofOp o harg
  let localCfg := finiteEmbedCfg (encodeBitwiseLabel (boundPC p pc) kind bo)
    (operandEvalStartCfg
      (R := ZipInstructionTailLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare := finite_step_prepare_entry hbound (boundPC p pc)
    (bitwiseInstr kind o) (instrClass (bitwiseInstr kind o))
    (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg
        (.control (.data (boundPC p pc) (instrClass (bitwiseInstr kind o))))
        state (coreStacks w s)) = some localCfg := by
    rw [hprepare]
    cases kind <;>
      simp [bitwiseInstr, finitePrepareInstr, finiteInitializeEntry,
        instrArgument, localCfg, operandEvalStartCfg_coreStacks,
        finiteEmbedCfg, mapLabelCfg, finiteInterpreterCfg]
    all_goals cases o <;> simp [bo, BoundedOp.ofOp] <;>
      constructor <;> congr
  rcases finite_bitwise_to_fetch hbound (boundPC p pc) kind bo w s hm state with
    ⟨localSteps, hlocalBound, finalState, hdispatch, hlocal⟩
  have hall := finite_data_prefix hbound hfetch (by cases kind <;> simp [bitwiseInstr])
    (by cases kind <;> simp [bitwiseInstr]) state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with acc :=
        (kind.natFn w s.acc (operandWordValue w bo.toOp s.mem) % 2 ^ w)}))
    hentry hlocal
  refine ⟨2 + localSteps, by omega, finalState, hdispatch, ?_⟩
  have hword : operandWordValue w o s.mem = sparseValue w o s.mem % 2 ^ w := rfl
  have hnat : kind.natFn w s.acc (operandWordValue w o s.mem) % 2 ^ w =
      kind.natFn w s.acc (sparseValue w o s.mem) % 2 ^ w := by
    have hbits : fixedBits w (kind.natFn w s.acc (operandWordValue w o s.mem)) =
        fixedBits w (kind.natFn w s.acc (sparseValue w o s.mem)) := by
      rw [fixedBits_bitwiseKind, fixedBits_bitwiseKind, hword,
        fixedBits_mod_word]
    simpa only [bitsValue_fixedBits] using congrArg bitsValue hbits
  simpa [bo, hnat] using hall

def shiftInstr (rightShift : Bool) (o : Op) : Instr :=
  if rightShift then .shiftr o else .shiftl o

def shiftValue (rightShift : Bool) (w accumulator count : Nat) : Nat :=
  if rightShift then accumulator / 2 ^ count % 2 ^ w
  else accumulator * 2 ^ count % 2 ^ w

set_option maxHeartbeats 1800000 in
theorem finite_shift_instruction {p : Program} {N pc w : Nat}
    (hbound : programArgumentBound p <= N) (rightShift : Bool) (o : Op)
    (hfetch : p[pc]? = some (shiftInstr rightShift o))
    (hw : 0 < w) (s : SparseState) (hacc : s.acc < 2 ^ w)
    (hm : s.mem.Normalized w) (state : FullInterpreterState N) :
    ∃ steps, steps <= shiftInstructionBound w s.mem + 3 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc :=
          (shiftValue rightShift w s.acc (sparseValue w o s.mem))})) := by
  have hargument : instrArgument (shiftInstr rightShift o) = operandArgument o := by
    cases rightShift <;> rfl
  let harg : operandArgument o <= N := by
    rw [← hargument]
    exact (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo := BoundedOp.ofOp o harg
  let localCfg := finiteEmbedCfg
    (encodeShiftLabel (boundPC p pc) rightShift bo)
    (operandEvalStartCfg
      (R := FullShiftLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare := finite_step_prepare_entry hbound (boundPC p pc)
    (shiftInstr rightShift o) (instrClass (shiftInstr rightShift o))
    (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry : TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg
        (.control (.data (boundPC p pc) (instrClass (shiftInstr rightShift o))))
        state (coreStacks w s)) = some localCfg := by
    rw [hprepare]
    cases rightShift <;>
      simp [shiftInstr, finitePrepareInstr, finiteInitializeEntry,
        instrArgument, localCfg, operandEvalStartCfg_coreStacks,
        finiteEmbedCfg, mapLabelCfg, finiteInterpreterCfg]
    all_goals cases o <;> simp [bo, BoundedOp.ofOp] <;>
      constructor <;> congr
  have hlocal : ∃ localSteps,
      localSteps <= shiftInstructionBound w s.mem + 1 ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[localSteps])
        (some localCfg) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc := (shiftValue rightShift w s.acc
          (sparseValue w bo.toOp s.mem))})) := by
    cases rightShift
    · simpa [localCfg, shiftValue] using
        finite_shiftLeft_to_fetch hbound (boundPC p pc) bo w hw s hacc hm state
    · simpa [localCfg, shiftValue] using
        finite_shiftRight_to_fetch hbound (boundPC p pc) bo w hw s hacc hm state
  rcases hlocal with
    ⟨localSteps, hlocalBound, finalState, hdispatch, hlocalRun⟩
  have hall := finite_data_prefix hbound hfetch
    (by cases rightShift <;> simp [shiftInstr])
    (by cases rightShift <;> simp [shiftInstr])
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with acc := (shiftValue rightShift w s.acc
        (sparseValue w bo.toOp s.mem))})) hentry hlocalRun
  refine ⟨2 + localSteps, by omega, finalState, hdispatch, ?_⟩
  simpa [bo] using hall

/-- A deliberately coarse uniform bound for simulating any data instruction.
It is a sum rather than a maximum so each instruction bound discharges by
linear arithmetic and the eventual polynomial estimate stays transparent. -/
def finiteDataStepBound (w : Nat) (m : SparseMemory) : Nat :=
  3 + readInstructionBound w m + writeInstructionBound w m +
    loadInstructionBound w m + storeInstructionBound w m +
    storeIndInstructionBound w m + addInstructionBound w m +
    subtractInstructionBound w m + mulInstructionBound w m +
    divideInstructionTotalBound w m + zipInstructionBound w m +
    shiftInstructionBound w m

theorem readInstructionBound_le_finiteDataStepBound (w : Nat) (m : SparseMemory) :
    readInstructionBound w m + 3 <= finiteDataStepBound w m := by
  simp [finiteDataStepBound]
  omega

theorem writeInstructionBound_le_finiteDataStepBound (w : Nat) (m : SparseMemory) :
    writeInstructionBound w m + 3 <= finiteDataStepBound w m := by
  simp [finiteDataStepBound]
  omega

theorem loadInstructionBound_le_finiteDataStepBound (w : Nat) (m : SparseMemory) :
    loadInstructionBound w m + 3 <= finiteDataStepBound w m := by
  simp [finiteDataStepBound]
  omega

theorem storeInstructionBound_le_finiteDataStepBound (w : Nat) (m : SparseMemory) :
    storeInstructionBound w m + 3 <= finiteDataStepBound w m := by
  simp [finiteDataStepBound]
  omega

theorem storeIndInstructionBound_le_finiteDataStepBound (w : Nat)
    (m : SparseMemory) :
    storeIndInstructionBound w m + 3 <= finiteDataStepBound w m := by
  simp [finiteDataStepBound]
  omega

theorem addInstructionBound_le_finiteDataStepBound (w : Nat) (m : SparseMemory) :
    addInstructionBound w m + 3 <= finiteDataStepBound w m := by
  simp [finiteDataStepBound]
  omega

theorem subtractInstructionBound_le_finiteDataStepBound (w : Nat)
    (m : SparseMemory) :
    subtractInstructionBound w m + 3 <= finiteDataStepBound w m := by
  simp [finiteDataStepBound]
  omega

theorem mulInstructionBound_le_finiteDataStepBound (w : Nat) (m : SparseMemory) :
    mulInstructionBound w m + 3 <= finiteDataStepBound w m := by
  simp [finiteDataStepBound]
  omega

theorem divideInstructionBound_le_finiteDataStepBound (w : Nat)
    (m : SparseMemory) :
    divideInstructionTotalBound w m + 3 <= finiteDataStepBound w m := by
  simp [finiteDataStepBound]
  omega

theorem zipInstructionBound_le_finiteDataStepBound (w : Nat) (m : SparseMemory) :
    zipInstructionBound w m + 3 <= finiteDataStepBound w m := by
  simp [finiteDataStepBound]
  omega

theorem shiftInstructionBound_le_finiteDataStepBound (w : Nat)
    (m : SparseMemory) :
    shiftInstructionBound w m + 3 <= finiteDataStepBound w m := by
  simp [finiteDataStepBound]
  omega

theorem finite_jump_instruction {p : Program} {N pc target : Nat}
    (hbound : programArgumentBound p <= N)
    (hfetch : p[pc]? = some (.jump target))
    (state : FullInterpreterState N) (tapes : CoreStack -> List SparseSymbol) :
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes) =
    some (finiteInterpreterCfg (.fetch (jumpPC p target)) state tapes) := by
  have hpc : pc < p.length := fetch_some_pc_lt hfetch
  have hget : p[pc] = .jump target := by
    simpa [List.getElem?_eq_getElem hpc] using hfetch
  simp [finiteInterpreterProgram, finiteControlStmt, finiteInterpreterCfg,
    controlDispatchMachine, fetch_boundPC, hfetch, hget, mapLabelStmt,
    lensRenameStmt, coreIdentityRenaming, FullInterpreterState.dispatchLens,
    FullInterpreterState.macroLens, InterpreterMacroState.dispatchLens,
    StateLens.comp, TM2.step, finiteEmbedControlLabel]

theorem finite_halt_fetch {p : Program} {N pc : Nat}
    (hbound : programArgumentBound p <= N)
    (hfetch : p[pc]? = some .halt)
    (state : FullInterpreterState N) (tapes : CoreStack -> List SparseSymbol) :
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes) =
    some (finiteInterpreterCfg (.control .stopped) state tapes) := by
  have hpc : pc < p.length := fetch_some_pc_lt hfetch
  have hget : p[pc] = .halt := by
    simpa [List.getElem?_eq_getElem hpc] using hfetch
  simp [finiteInterpreterProgram, finiteControlStmt, finiteInterpreterCfg,
    controlDispatchMachine, fetch_boundPC, hfetch, hget, mapLabelStmt,
    lensRenameStmt, coreIdentityRenaming, FullInterpreterState.dispatchLens,
    FullInterpreterState.macroLens, InterpreterMacroState.dispatchLens,
    StateLens.comp, TM2.step, finiteEmbedControlLabel]

theorem finite_missing_fetch {p : Program} {N pc : Nat}
    (hbound : programArgumentBound p <= N)
    (hfetch : p[pc]? = none)
    (state : FullInterpreterState N) (tapes : CoreStack -> List SparseSymbol) :
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes) =
    some (finiteInterpreterCfg (.control .stopped) state tapes) := by
  simp [finiteInterpreterProgram, finiteControlStmt, finiteInterpreterCfg,
    controlDispatchMachine, fetch_boundPC, hfetch, mapLabelStmt,
    lensRenameStmt, coreIdentityRenaming, FullInterpreterState.dispatchLens,
    FullInterpreterState.macroLens, InterpreterMacroState.dispatchLens,
    StateLens.comp, TM2.step, finiteEmbedControlLabel]

theorem finite_sparseHalt_to_stopped {p : Program} {N w : Nat}
    (hbound : programArgumentBound p <= N) (s : SparseState)
    (hm : s.mem.Normalized w) (hstop : sparseStep w p s = none)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= operandEvalBound w s.mem + 4 ∧
      ∃ finalState finalTapes,
        finalTapes .output = (coreStacks w s) .output ∧
        ((fun x => x.bind (TM2.step
          (finiteInterpreterProgram p N hbound)))^[steps])
          (some (finiteInterpreterCfg (.fetch (boundPC p s.pc)) state
            (coreStacks w s))) =
        some (finiteInterpreterCfg (.control .stopped) finalState finalTapes) := by
  unfold sparseStep at hstop
  cases hfetch : p[s.pc]? with
  | none =>
      refine ⟨1, by simp [operandEvalBound], state, coreStacks w s, rfl, ?_⟩
      simpa [Function.iterate_one] using
        finite_missing_fetch hbound hfetch state (coreStacks w s)
  | some i =>
      simp [hfetch] at hstop
      cases i with
      | read address =>
          cases hinp : s.inp with
          | nil =>
              exact finite_read_exhausted hbound hfetch s hinp hm state
          | cons value tail => simp [sparseEffect, hinp] at hstop
      | halt =>
          refine ⟨1, by simp [operandEvalBound], state, coreStacks w s, rfl, ?_⟩
          simpa [Function.iterate_one] using
            finite_halt_fetch hbound hfetch state (coreStacks w s)
      | write o => simp [sparseEffect] at hstop
      | load o => simp [sparseEffect] at hstop
      | store address => simp [sparseEffect] at hstop
      | storeInd address => simp [sparseEffect] at hstop
      | add o => simp [sparseEffect] at hstop
      | sub o => simp [sparseEffect] at hstop
      | mul o => simp [sparseEffect] at hstop
      | div o => simp [sparseEffect] at hstop
      | and o => simp [sparseEffect] at hstop
      | or o => simp [sparseEffect] at hstop
      | xor o => simp [sparseEffect] at hstop
      | compl o => simp [sparseEffect] at hstop
      | shiftl o => simp [sparseEffect] at hstop
      | shiftr o => simp [sparseEffect] at hstop
      | jump target => simp [sparseEffect] at hstop
      | jzero target => simp [sparseEffect] at hstop
      | jgtz target => simp [sparseEffect] at hstop

theorem finite_stopped_halts {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N)
    (state : FullInterpreterState N) (tapes : CoreStack -> List SparseSymbol) :
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control .stopped) state tapes) =
    some ⟨none, state, tapes⟩ := by
  simp [finiteInterpreterProgram, finiteControlStmt, finiteInterpreterCfg,
    controlDispatchMachine, mapLabelStmt, lensRenameStmt,
    coreIdentityRenaming, FullInterpreterState.dispatchLens,
    FullInterpreterState.macroLens, InterpreterMacroState.dispatchLens,
    StateLens.comp, TM2.step]

def finiteControlCfg {p : Program} {N : Nat}
    (c : (controlDispatchMachine p).Cfg) (ambient : FullInterpreterState N) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) where
  l := c.l.map finiteEmbedControlLabel
  var := FullInterpreterState.dispatchLens.put ambient c.var
  stk := c.stk

set_option maxHeartbeats 1000000 in
theorem finiteControl_step_of_some {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N)
    (c d : (controlDispatchMachine p).Cfg)
    (ambient : FullInterpreterState N)
    (hstep : (controlDispatchMachine p).step c = some d)
    (hdlabel : d.l.isSome) :
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteControlCfg c ambient) = some (finiteControlCfg d ambient) := by
  rcases c with ⟨label, control, tapes⟩
  cases label with
  | none => simp [TM2.step] at hstep
  | some label =>
      have liftControl
          (hprogram : finiteInterpreterProgram p N hbound
            (finiteEmbedControlLabel label) = finiteControlStmt label) :
          TM2.step (finiteInterpreterProgram p N hbound)
            (finiteControlCfg ⟨some label, control, tapes⟩ ambient) =
              some (finiteControlCfg d ambient) := by
        have hd : TM2.stepAux ((controlDispatchMachine p).m label) control tapes = d := by
          exact Option.some.inj hstep
        change some (TM2.stepAux
          (finiteInterpreterProgram p N hbound (finiteEmbedControlLabel label))
          (FullInterpreterState.dispatchLens.put ambient control) tapes) =
            some (finiteControlCfg d ambient)
        subst d
        rw [hprogram]
        simp only [finiteControlStmt, stepAux_mapLabelStmt]
        have htapes : renamedStacks coreIdentityRenaming tapes tapes = tapes := by
          funext k
          simp [renamedStacks, coreIdentityRenaming]
        have hlens := stepAux_lensRenameStmt
          (Λx := Empty) coreIdentityRenaming FullInterpreterState.dispatchLens
          ((controlDispatchMachine p).m label) control ambient tapes tapes
        have hlens' : TM2.stepAux
            (lensRenameStmt (Λx := Empty) coreIdentityRenaming
              FullInterpreterState.dispatchLens ((controlDispatchMachine p).m label))
            (FullInterpreterState.dispatchLens.put ambient control) tapes =
          lensRenamedCfg coreIdentityRenaming FullInterpreterState.dispatchLens
            (TM2.stepAux ((controlDispatchMachine p).m label) control tapes)
            ambient tapes := by
          simpa only [htapes] using hlens
        rw [hlens']
        generalize he : TM2.stepAux ((controlDispatchMachine p).m label)
          control tapes = e
        rcases e with ⟨elabel, econtrol, estacks⟩
        have hembed := congrArg
          (fun c => mapLabelCfg
            (fun x : Sum (ControlDispatchLabel p) Empty => match x with
              | Sum.inl l => finiteEmbedControlLabel (N := N) l
              | Sum.inr e => nomatch e)
            (lensRenamedCfg coreIdentityRenaming
              FullInterpreterState.dispatchLens c ambient tapes)) he
        apply congrArg some
        refine hembed.trans ?_
        have hestacks : renamedStacks coreIdentityRenaming estacks tapes = estacks := by
          funext k
          simp [renamedStacks, coreIdentityRenaming]
        cases elabel with
        | none =>
            simp [finiteControlCfg, lensRenamedCfg, mapLabelCfg, hestacks,
              FullInterpreterState.dispatchLens] <;> rfl
        | some elabel =>
            cases elabel <;>
              simp [finiteControlCfg, lensRenamedCfg, mapLabelCfg, hestacks,
                FullInterpreterState.dispatchLens, finiteEmbedControlLabel] <;> rfl
      cases label with
      | fetch pc => exact liftControl rfl
      | scanAccumulator pc target z => exact liftControl rfl
      | restoreAccumulator pc target z => exact liftControl rfl
      | data pc kind =>
          have hdnone : d.l = none := by
            have := congrArg (fun x => x.l) (Option.some.inj hstep)
            simpa [controlDispatchMachine, TM2.step] using this.symm
          rw [hdnone] at hdlabel
          simp at hdlabel
      | stopped =>
          have hdnone : d.l = none := by
            have := congrArg (fun x => x.l) (Option.some.inj hstep)
            simpa [controlDispatchMachine, TM2.step] using this.symm
          rw [hdnone] at hdlabel
          simp at hdlabel

theorem finiteControl_run_of_some {p : Program} {N n : Nat}
    (hbound : programArgumentBound p <= N)
    (c d : (controlDispatchMachine p).Cfg)
    (ambient : FullInterpreterState N)
    (hrun : ((fun x : Option (controlDispatchMachine p).Cfg =>
      x.bind (controlDispatchMachine p).step)^[n]) (some c) = some d)
    (hdlabel : d.l.isSome) :
    ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[n])
      (some (finiteControlCfg c ambient)) =
    some (finiteControlCfg d ambient) := by
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply] at hrun ⊢
      cases hrun
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      simp only [Option.bind_some] at hrun ⊢
      cases hs : (controlDispatchMachine p).step c with
      | none =>
          change ((fun x : Option (controlDispatchMachine p).Cfg =>
            x.bind (controlDispatchMachine p).step)^[n])
              ((controlDispatchMachine p).step c) = some d at hrun
          rw [hs, iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          have hc'label : c'.l.isSome := by
            cases n with
            | zero =>
                simp only [Function.iterate_zero_apply] at hrun
                rw [hs] at hrun
                cases hrun
                exact hdlabel
            | succ n =>
                rw [hs] at hrun
                rcases c' with ⟨none | label, control, tapes⟩
                · change ((fun x : Option (controlDispatchMachine p).Cfg =>
                    x.bind (controlDispatchMachine p).step)^[n + 1])
                      (some ⟨none, control, tapes⟩) = some d at hrun
                  rw [Function.iterate_succ_apply] at hrun
                  change ((fun x : Option (controlDispatchMachine p).Cfg =>
                    x.bind (controlDispatchMachine p).step)^[n]) none = some d at hrun
                  rw [iterate_optionBind_none] at hrun
                  contradiction
                · rfl
          rw [finiteControl_step_of_some hbound c c' ambient hs hc'label]
          rw [hs] at hrun
          exact ih c' hrun

theorem finiteControlCfg_boundary {p : Program} {N pc w : Nat}
    (s : SparseState) (state : FullInterpreterState N)
    (hdispatch : FullInterpreterState.dispatchLens.get state = default) :
    finiteControlCfg (controlBoundaryCfg p pc w s) state =
      finiteInterpreterCfg (.fetch (boundPC p pc)) state (coreStacks w s) := by
  unfold finiteControlCfg controlBoundaryCfg controlDispatchCfg
  unfold finiteInterpreterCfg
  rw [← hdispatch, FullInterpreterState.dispatchLens.put_get]
  rfl

theorem finite_jzero_instruction {p : Program} {N pc target w : Nat}
    (hbound : programArgumentBound p <= N)
    (hfetch : p[pc]? = some (.jzero target))
    (s : SparseState) (hacc : s.acc < 2 ^ w)
    (state : FullInterpreterState N)
    (hdispatch : FullInterpreterState.dispatchLens.get state = default) :
    let next := if s.acc = 0 then target else pc + 1
    ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[2 * w + 3])
      (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
        (coreStacks w s))) =
    some (finiteInterpreterCfg (.fetch (boundPC p next)) state
      (coreStacks w {s with pc := next})) := by
  dsimp only
  have hrun := control_jzero_correct hfetch hacc
  have hlift := finiteControl_run_of_some hbound
    (controlBoundaryCfg p pc w s)
    (controlBoundaryCfg p (if s.acc = 0 then target else pc + 1) w
      {s with pc := if s.acc = 0 then target else pc + 1}) state hrun
    (by rfl)
  rw [finiteControlCfg_boundary s state hdispatch] at hlift
  rw [finiteControlCfg_boundary
    {s with pc := if s.acc = 0 then target else pc + 1} state hdispatch] at hlift
  exact hlift

theorem finite_jgtz_instruction {p : Program} {N pc target w : Nat}
    (hbound : programArgumentBound p <= N)
    (hfetch : p[pc]? = some (.jgtz target))
    (s : SparseState) (hacc : s.acc < 2 ^ w)
    (state : FullInterpreterState N)
    (hdispatch : FullInterpreterState.dispatchLens.get state = default) :
    let next := if 0 < s.acc then target else pc + 1
    ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[2 * w + 3])
      (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
        (coreStacks w s))) =
    some (finiteInterpreterCfg (.fetch (boundPC p next)) state
      (coreStacks w {s with pc := next})) := by
  dsimp only
  have hrun := control_jgtz_correct hfetch hacc
  have hlift := finiteControl_run_of_some hbound
    (controlBoundaryCfg p pc w s)
    (controlBoundaryCfg p (if 0 < s.acc then target else pc + 1) w
      {s with pc := if 0 < s.acc then target else pc + 1}) state hrun
    (by rfl)
  rw [finiteControlCfg_boundary s state hdispatch] at hlift
  rw [finiteControlCfg_boundary
    {s with pc := if 0 < s.acc then target else pc + 1} state hdispatch] at hlift
  exact hlift

def isDataInstr : Instr -> Prop
  | .jump _ | .jzero _ | .jgtz _ | .halt => False
  | _ => True

set_option maxHeartbeats 0 in
theorem finite_data_effect {p : Program} {N w : Nat}
    (hbound : programArgumentBound p <= N) (hw : 0 < w)
    (s : SparseState) (hacc : s.acc < 2 ^ w) (hm : s.mem.Normalized w)
    (i : Instr) (hfetch : p[s.pc]? = some i) (hdata : isDataInstr i)
    {s' : SparseState} (heffect : sparseEffect w i s = some s')
    (state : FullInterpreterState N) :
    ∃ steps, steps <= finiteDataStepBound w s.mem ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p s.pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (boundPC p s'.pc)) finalState
        (coreStacks w s')) := by
  have hpc : s.pc < p.length := fetch_some_pc_lt hfetch
  have hnext : nextPC p (boundPC p s.pc) = boundPC p (s.pc + 1) :=
    nextPC_boundPC_of_lt hpc
  cases i with
  | read address =>
      cases hin : s.inp with
      | nil => simp [sparseEffect, hin] at heffect
      | cons value inputTail =>
          simp [sparseEffect, hin] at heffect
          subst s'
          rcases finite_read_instruction hbound address value inputTail hfetch
              s hin hm state with
            ⟨steps, hs, finalState, hdispatch, hrun⟩
          refine ⟨steps, hs.trans (readInstructionBound_le_finiteDataStepBound _ _),
            finalState, hdispatch, ?_⟩
          simpa [hnext, coreStacks] using hrun
  | write o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_write_instruction hbound o hfetch s hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (writeInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [hnext, coreStacks] using hrun
  | load o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_load_instruction hbound o hfetch s hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (loadInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [hnext, operandWordValue, coreStacks] using hrun
  | store address =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_store_instruction hbound address hfetch s hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (storeInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [hnext, coreStacks] using hrun
  | storeInd address =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_storeInd_instruction hbound address hfetch s hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (storeIndInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [hnext, coreStacks] using hrun
  | add o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_add_instruction hbound o hfetch s hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (addInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [hnext, coreStacks] using hrun
  | sub o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_sub_instruction hbound o hfetch s hacc hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (subtractInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [hnext, coreStacks] using hrun
  | mul o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_mul_instruction hbound o hfetch hw s hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (mulInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [hnext, coreStacks] using hrun
  | div o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_div_instruction hbound o hfetch s hacc hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (divideInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [hnext, coreStacks] using hrun
  | and o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_bitwise_instruction hbound .and o hfetch s hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (zipInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [bitwiseInstr, BitwiseKind.natFn, hnext, coreStacks] using hrun
  | or o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_bitwise_instruction hbound .or o hfetch s hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (zipInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [bitwiseInstr, BitwiseKind.natFn, hnext, coreStacks] using hrun
  | xor o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_bitwise_instruction hbound .xor o hfetch s hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (zipInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [bitwiseInstr, BitwiseKind.natFn, hnext, coreStacks] using hrun
  | compl o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_bitwise_instruction hbound .compl o hfetch s hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (zipInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [bitwiseInstr, BitwiseKind.natFn, hnext, coreStacks] using hrun
  | shiftl o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_shift_instruction hbound false o hfetch hw s hacc hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (shiftInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [shiftInstr, shiftValue, hnext, coreStacks] using hrun
  | shiftr o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_shift_instruction hbound true o hfetch hw s hacc hm state with
        ⟨steps, hs, finalState, hdispatch, hrun⟩
      refine ⟨steps, hs.trans (shiftInstructionBound_le_finiteDataStepBound _ _),
        finalState, hdispatch, ?_⟩
      simpa [shiftInstr, shiftValue, hnext, coreStacks] using hrun
  | jump _ | jzero _ | jgtz _ | halt => simp [isDataInstr] at hdata

def finiteStepBound (w : Nat) (m : SparseMemory) : Nat :=
  finiteDataStepBound w m + (2 * w + 4)

set_option maxHeartbeats 0 in
theorem finite_sparseStep_correct {p : Program} {N w : Nat}
    (hbound : programArgumentBound p <= N) (hw : 0 < w)
    (s s' : SparseState) (hacc : s.acc < 2 ^ w)
    (hm : s.mem.Normalized w) (hstep : sparseStep w p s = some s')
    (state : FullInterpreterState N)
    (hdispatch : FullInterpreterState.dispatchLens.get state = default) :
    ∃ steps, steps <= finiteStepBound w s.mem ∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state ∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p s.pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (boundPC p s'.pc)) finalState
        (coreStacks w s')) := by
  unfold sparseStep at hstep
  cases hfetch : p[s.pc]? with
  | none => simp [hfetch] at hstep
  | some i =>
      simp [hfetch] at hstep
      by_cases hdata : isDataInstr i
      · rcases finite_data_effect (p := p) (N := N) (w := w)
            hbound hw s hacc hm i hfetch hdata hstep state with
          ⟨steps, hs, finalState, hfinalDispatch, hrun⟩
        refine ⟨steps, ?_, finalState, hfinalDispatch, hrun⟩
        exact hs.trans (by unfold finiteStepBound; omega)
      · cases i with
        | jump target =>
            simp [sparseEffect] at hstep
            subst s'
            refine ⟨1, ?_, state, rfl, ?_⟩
            · unfold finiteStepBound
              omega
            have hjump := finite_jump_instruction hbound hfetch state
              (coreStacks w s)
            simpa [jumpPC, coreStacks, Function.iterate_one] using hjump
        | jzero target =>
            simp [sparseEffect] at hstep
            subst s'
            refine ⟨2 * w + 3, by simp [finiteStepBound]; omega,
              state, rfl, ?_⟩
            simpa [coreStacks] using
              finite_jzero_instruction hbound hfetch s hacc state hdispatch
        | jgtz target =>
            simp [sparseEffect] at hstep
            subst s'
            refine ⟨2 * w + 3, by simp [finiteStepBound]; omega,
              state, rfl, ?_⟩
            simpa [coreStacks] using
              finite_jgtz_instruction hbound hfetch s hacc state hdispatch
        | halt => simp [sparseEffect] at hstep
        | read _ => simp [isDataInstr] at hdata
        | write _ => simp [isDataInstr] at hdata
        | load _ => simp [isDataInstr] at hdata
        | store _ => simp [isDataInstr] at hdata
        | storeInd _ => simp [isDataInstr] at hdata
        | add _ => simp [isDataInstr] at hdata
        | sub _ => simp [isDataInstr] at hdata
        | mul _ => simp [isDataInstr] at hdata
        | div _ => simp [isDataInstr] at hdata
        | and _ => simp [isDataInstr] at hdata
        | or _ => simp [isDataInstr] at hdata
        | xor _ => simp [isDataInstr] at hdata
        | compl _ => simp [isDataInstr] at hdata
        | shiftl _ => simp [isDataInstr] at hdata
        | shiftr _ => simp [isDataInstr] at hdata

theorem sparseEffect_acc_lt {w : Nat} (hw : 0 < w) {i : Instr}
    {s s' : SparseState} (hacc : s.acc < 2 ^ w)
    (h : sparseEffect w i s = some s') : s'.acc < 2 ^ w := by
  cases i <;> simp [sparseEffect] at h
  case read address =>
    cases hin : s.inp with
    | nil => simp [hin] at h
    | cons value tail =>
        simp [hin] at h
        subst s'
        exact hacc
  all_goals
    subst s'
    first
    | exact hacc
    | exact Nat.mod_lt _ (by positivity)

theorem sparseStep_acc_lt {w : Nat} (hw : 0 < w) {p : Program}
    {s s' : SparseState} (hacc : s.acc < 2 ^ w)
    (h : sparseStep w p s = some s') : s'.acc < 2 ^ w := by
  unfold sparseStep at h
  cases hi : p[s.pc]? with
  | none => simp [hi] at h
  | some i =>
      simp [hi] at h
      exact sparseEffect_acc_lt hw hacc h

theorem sparseRun_acc_lt {w : Nat} (hw : 0 < w) {p : Program} {t : Nat}
    {s s' : SparseState} (hacc : s.acc < 2 ^ w)
    (h : sparseRun w p t s = some s') : s'.acc < 2 ^ w := by
  induction t generalizing s with
  | zero =>
      simp [sparseRun] at h
      subst s'
      exact hacc
  | succ t ih =>
      simp only [sparseRun] at h
      cases hs : sparseStep w p s with
      | none => simp [hs] at h
      | some s₁ =>
          simp [hs] at h
          exact ih (sparseStep_acc_lt hw hacc hs) h

theorem finiteStepBound_mono_length {w : Nat} {m₁ m₂ : SparseMemory}
    (h : m₁.length <= m₂.length) :
    finiteStepBound w m₁ <= finiteStepBound w m₂ := by
  simp [finiteStepBound, finiteDataStepBound, readInstructionBound,
    writeInstructionBound, loadInstructionBound, storeInstructionBound,
    storeIndInstructionBound, addInstructionBound, subtractInstructionBound,
    mulInstructionBound, divideInstructionTotalBound, zipInstructionBound,
    shiftInstructionBound, operandEvalBound]
  nlinarith

def finiteRunUnitBound (w initialMemoryLength t : Nat) : Nat :=
  finiteStepBound w (List.replicate (initialMemoryLength + t) (0, 0))

set_option maxHeartbeats 3500000 in
theorem finite_sparseRun_correct {p : Program} {N w t : Nat}
    (hbound : programArgumentBound p <= N) (hw : 0 < w)
    (s s' : SparseState) (hacc : s.acc < 2 ^ w)
    (hm : s.mem.Normalized w) (hrun : sparseRun w p t s = some s')
    (state : FullInterpreterState N)
    (hdispatch : FullInterpreterState.dispatchLens.get state = default) :
    ∃ steps, steps <= t * finiteRunUnitBound w s.mem.length t ∧
      ∃ finalState,
        FullInterpreterState.dispatchLens.get finalState = default ∧
        ((fun x => x.bind
          (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
          (some (finiteInterpreterCfg (.fetch (boundPC p s.pc)) state
            (coreStacks w s))) =
        some (finiteInterpreterCfg (.fetch (boundPC p s'.pc)) finalState
          (coreStacks w s')) := by
  induction t generalizing s state with
  | zero =>
      simp [sparseRun] at hrun
      subst s'
      exact ⟨0, by simp, state, hdispatch, rfl⟩
  | succ t ih =>
      simp only [sparseRun] at hrun
      cases hs : sparseStep w p s with
      | none => simp [hs] at hrun
      | some s₁ =>
          simp [hs] at hrun
          have hacc₁ := sparseStep_acc_lt hw hacc hs
          have hm₁ := sparseStep_mem_normalized hm hs
          rcases finite_sparseStep_correct hbound hw s s₁ hacc hm hs state
              hdispatch with
            ⟨firstSteps, hfirstBound, middleState, hmiddleDispatch, hfirst⟩
          have hmiddleDefault :
              FullInterpreterState.dispatchLens.get middleState = default :=
            hmiddleDispatch.trans hdispatch
          rcases ih s₁ hacc₁ hm₁ hrun middleState hmiddleDefault with
            ⟨restSteps, hrestBound, finalState, hfinalDispatch, hrest⟩
          let targetMemory : SparseMemory :=
            List.replicate (s.mem.length + (t + 1)) (0, 0)
          have hlen₁ : s₁.mem.length <= s.mem.length + 1 :=
            sparseStep_mem_length_le hs
          have hfirstUnit : finiteStepBound w s.mem <=
              finiteStepBound w targetMemory := by
            apply finiteStepBound_mono_length
            simp [targetMemory]
          have hrestUnit : finiteRunUnitBound w s₁.mem.length t <=
              finiteStepBound w targetMemory := by
            unfold finiteRunUnitBound
            apply finiteStepBound_mono_length
            simp [targetMemory]
            omega
          have htotalBound : firstSteps + restSteps <=
              (t + 1) * finiteRunUnitBound w s.mem.length (t + 1) := by
            have hf := hfirstBound.trans hfirstUnit
            have hr := hrestBound.trans (Nat.mul_le_mul_left t hrestUnit)
            have hadd := Nat.add_le_add hf hr
            simpa [finiteRunUnitBound, targetMemory, Nat.add_mul,
              Nat.add_comm] using hadd
          have hchain := chain_iterations
            (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
              (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
              x.bind (TM2.step (finiteInterpreterProgram p N hbound)))
            hfirst hrest
          exact ⟨firstSteps + restSteps, htotalBound, finalState,
            hfinalDispatch, hchain⟩

theorem cappedShiftLoopBound_closed (w fuel : Nat) :
    cappedShiftLoopBound w fuel = fuel * (6 * w + 14) + 3 * w + 7 := by
  induction fuel with
  | zero => simp [cappedShiftLoopBound]
  | succ fuel ih =>
      simp only [cappedShiftLoopBound]
      rw [ih]
      ring

theorem finiteStepBound_polynomial (w : Nat) (m : SparseMemory) :
    finiteStepBound w m <= 1000 * (m.length + 1) * (w + 1) ^ 2 := by
  simp [finiteStepBound, finiteDataStepBound, readInstructionBound,
    writeInstructionBound, loadInstructionBound, storeInstructionBound,
    storeIndInstructionBound, addInstructionBound, subtractInstructionBound,
    mulInstructionBound, divideInstructionTotalBound, zipInstructionBound,
    shiftInstructionBound, operandEvalBound, divRunTimeBound, fullShiftBound,
    shiftCoreBound, shiftSetupBound, cappedShiftLoopBound_closed]
  ring_nf at *
  nlinarith

theorem finiteSparseRun_steps_polynomial {w t initialMemoryLength steps : Nat}
    (hsteps : steps <= t * finiteRunUnitBound w initialMemoryLength t) :
    steps <= 1000 * t * (initialMemoryLength + t + 1) * (w + 1) ^ 2 := by
  apply hsteps.trans
  unfold finiteRunUnitBound
  have h := finiteStepBound_polynomial w
    (List.replicate (initialMemoryLength + t) (0, 0))
  simp only [List.length_replicate] at h
  nlinarith

noncomputable def coreSimulationPolynomial
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C 1000 * timeBound * (timeBound + 1) *
    (wordBound + 2) ^ 2

@[simp] theorem coreSimulationPolynomial_eval
    (wordBound timeBound : Polynomial Nat) (n : Nat) :
    (coreSimulationPolynomial wordBound timeBound).eval n =
      1000 * timeBound.eval n * (timeBound.eval n + 1) *
        (wordBound.eval n + 2) ^ 2 := by
  simp [coreSimulationPolynomial]

theorem finiteSparseRun_steps_le_corePolynomial
    (wordBound timeBound : Polynomial Nat) (n w t steps : Nat)
    (hw : w = wordBound.eval n + 1) (ht : t <= timeBound.eval n)
    (hsteps : steps <= t * finiteRunUnitBound w 0 t) :
    steps <= (coreSimulationPolynomial wordBound timeBound).eval n := by
  have hcore := finiteSparseRun_steps_polynomial hsteps
  subst w
  rw [coreSimulationPolynomial_eval]
  calc
    steps <= 1000 * t * (0 + t + 1) *
        (wordBound.eval n + 1 + 1) ^ 2 := hcore
    _ <= 1000 * timeBound.eval n * (timeBound.eval n + 1) *
        (wordBound.eval n + 2) ^ 2 := by
      simp only [zero_add, Nat.add_assoc, Nat.add_left_cancel_iff]
      gcongr

set_option maxHeartbeats 2000000 in
theorem ramRunsTo_coreSimulation {p : Program} {w t : Nat}
    (hw : 0 < w) {input output : List Nat}
    (hram : RunsTo w p input output t) :
    ∃ (ss : SparseState) (steps : Nat),
      ss.out = output ∧ sparseStep w p ss = none ∧
      ss.mem.Normalized w ∧ ss.mem.length <= t ∧ ss.out.length <= t ∧
      steps <= t * finiteRunUnitBound w 0 t ∧
      ∃ finalState,
        FullInterpreterState.dispatchLens.get finalState = default ∧
        ((fun x => x.bind (TM2.step
          (finiteInterpreterProgram p (programArgumentBound p) le_rfl)))^[steps])
          (some (finiteInterpreterCfg (.fetch (boundPC p 0))
            (default : FullInterpreterState (programArgumentBound p))
            (coreStacks w (sparseInitState input)))) =
        some (finiteInterpreterCfg (.fetch (boundPC p ss.pc)) finalState
          (coreStacks w ss)) := by
  rcases sparse_halts_of_runsTo hram with
    ⟨ss, hsrun, hhalt, hout, hmem⟩
  have hacc0 : (sparseInitState input).acc < 2 ^ w := by
    simp [sparseInitState]
  rcases finite_sparseRun_correct (p := p) (N := programArgumentBound p)
      le_rfl hw (sparseInitState input) ss hacc0
      (SparseMemory.normalized_nil w) hsrun default rfl with
    ⟨steps, hsteps, finalState, hdispatch, htm⟩
  refine ⟨ss, steps, hout, hhalt,
    sparseRun_init_mem_normalized hsrun, hmem,
    sparseRun_init_out_length_le hsrun,
    hsteps, finalState, hdispatch, ?_⟩
  simpa [sparseInitState] using htm

end

end Lax51Proofs.RamToTM
