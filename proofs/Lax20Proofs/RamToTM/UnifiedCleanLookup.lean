import Lax20Proofs.RamToTM.UnifiedLookupPhase

namespace Lax20Proofs.RamToTM

open Turing TM2

inductive LookupDecisionLabel
  | decide
  deriving DecidableEq, Fintype, Inhabited

abbrev UnifiedCleanFinish (R : Type) := Sum ZeroWordLabel R
abbrev UnifiedCleanAfter (R : Type) :=
  Sum LookupDecisionLabel (UnifiedCleanFinish R)
abbrev UnifiedCleanTail (R : Type) :=
  Sum DiscardLabel (UnifiedCleanAfter R)
abbrev UnifiedCleanLookupLabel (R : Type) :=
  Sum LookupScanLabel (UnifiedCleanTail R)

def unifiedCleanFinishProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    UnifiedCleanFinish R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (UnifiedCleanFinish R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft zeroWordCoreRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done returnLabel)
    right

def lookupDecisionProgram {N : ℕ} {R : Type} (returnLabel : R) :
    LookupDecisionLabel → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (UnifiedCleanAfter R) (FullInterpreterState N)
  | .decide =>
      .branch FullInterpreterState.lookupFound
        (.goto fun _ => .inr (.inr returnLabel))
        (.goto fun _ => .inr (.inl ZeroWordLabel.fill))

def unifiedCleanAfterProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    UnifiedCleanAfter R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (UnifiedCleanAfter R) (FullInterpreterState N) :=
  liftRightProgram (lookupDecisionProgram returnLabel)
    (unifiedCleanFinishProgram returnLabel right)

def unifiedCleanTailProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    UnifiedCleanTail R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (UnifiedCleanTail R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl LookupDecisionLabel.decide))
    (unifiedCleanAfterProgram returnLabel right)

def unifiedCleanLookupProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    UnifiedCleanLookupLabel R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol)
      (UnifiedCleanLookupLabel R) (FullInterpreterState N) :=
  unifiedLookupProgram (unifiedCleanTailProgram returnLabel right)

def cleanDecisionCfg {N : ℕ} {R : Type}
    (state : FullInterpreterState N)
    (tapes : CoreStack → List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (UnifiedCleanAfter R) (FullInterpreterState N) where
  l := some (.inl .decide)
  var := state
  stk := tapes

def cleanReturnCfg {N : ℕ} {R : Type} (returnLabel : R)
    (state : FullInterpreterState N)
    (tapes : CoreStack → List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N) where
  l := some returnLabel
  var := state
  stk := tapes

@[simp] theorem lookupDecision_found_step {N : ℕ} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) R (FullInterpreterState N))
    (state : FullInterpreterState N) (hfound : state.lookupFound = true)
    (tapes : CoreStack → List SparseSymbol) :
    TM2.step (unifiedCleanAfterProgram returnLabel right)
      (cleanDecisionCfg (R := R) state tapes) =
    some (mapLabelCfg Sum.inr
      (mapLabelCfg Sum.inr (cleanReturnCfg returnLabel state tapes))) := by
  simp [unifiedCleanAfterProgram, lookupDecisionProgram, cleanDecisionCfg,
    cleanReturnCfg, liftRightProgram, mapLabelCfg, TM2.step, hfound]

theorem lookupDecision_missing_step {N : ℕ} {R : Type}
    (returnLabel : R) (right : R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) R (FullInterpreterState N))
    (w accumulator : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol)
    (state : FullInterpreterState N) (hmissing : state.lookupFound = false) :
    TM2.step (unifiedCleanAfterProgram returnLabel right)
      (cleanDecisionCfg (R := R) state
        (operandBoundaryBase w accumulator m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg (Λx := R) zeroWordCoreRenaming
        FullInterpreterState.zeroLens
        (zeroWordCfgState .fill
          (FullInterpreterState.zeroLens.get state)
          ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        state (operandBoundaryBase w accumulator m base))) := by
  simp [unifiedCleanAfterProgram, lookupDecisionProgram, cleanDecisionCfg,
    liftRightProgram, mapLabelCfg, TM2.step, hmissing,
    lensRenamedCfg, zeroWordCoreRenaming, zeroWordCoreDecode,
    zeroWordCfgState, zeroWordStacks, operandBoundaryBase, renamedStacks]
  constructor
  · rw [FullInterpreterState.zeroLens.put_get]
  · funext k
    cases k <;> rfl

theorem discard_decision_bridge {N : ℕ} {R : Type}
    (state : FullInterpreterState N)
    (tapes : CoreStack → List SparseSymbol)
    (hwork : tapes .work1 = []) :
    phaseReturnCfg (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (Sum.inl LookupDecisionLabel.decide : UnifiedCleanAfter R)
      (discardCfg .done []) state tapes =
    cleanDecisionCfg (R := R)
      (FullInterpreterState.moveLens.put state default) tapes := by
  simp [phaseReturnCfg, cleanDecisionCfg, discardCoreRenaming,
    discardCfg, discardStacks, renamedStacks]
  funext k
  cases k <;> simp [renamedStacks, discardCoreRenaming,
    discardCfg, discardStacks, hwork]

theorem zero_return_bridge {N : ℕ} {R : Type}
    (returnLabel : R) (w accumulator : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg zeroWordCoreRenaming FullInterpreterState.zeroLens
      returnLabel
      (zeroWordCfg .done
        ((fixedBits w accumulator).map SparseSymbol.bit) []
        ((fixedBits w 0).reverse.map SparseSymbol.bit))
      state (operandBoundaryBase w accumulator m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.zeroLens.put state default)
      (operandResultBase w accumulator 0 m base) := by
  simp [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    zeroWordCoreRenaming, zeroWordCoreDecode, zeroWordCfg,
    zeroWordStacks, operandBoundaryBase, operandResultBase,
    renamedStacks, fixedBits_zero, List.map_reverse]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks, zeroWordCoreRenaming,
      zeroWordCoreDecode, zeroWordCfg, zeroWordStacks,
      operandBoundaryBase, operandResultBase, fixedBits_zero,
      List.map_reverse]

theorem unifiedCleanLookup_found {N : ℕ} {R : Type}
    (w accumulator query value : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hfind : m.find? query = some value)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ∃ steps ≤ m.length * (12 * w + 22) + 12 * w + 26,
      ((fun o => o.bind (TM2.step
        (unifiedCleanLookupProgram returnLabel right)))^[steps])
        (some (lensRenamedCfg lookupCoreRenaming
          FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          state (operandBoundaryBase w accumulator m base))) =
      some (mapLabelCfg (fun l : UnifiedCleanTail R => Sum.inr l)
        (mapLabelCfg (fun l : UnifiedCleanAfter R => Sum.inr l)
          (mapLabelCfg (fun l : UnifiedCleanFinish R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (cleanReturnCfg returnLabel
                (FullInterpreterState.moveLens.put
                  (lookupRecordOutcome .found
                    (FullInterpreterState.lookupLens.put state
                      ⟨none, true, none, none⟩)) default)
                (operandResultBase w accumulator value m base)))))) := by
  let foundState := lookupRecordOutcome LookupScanLabel.found
    (FullInterpreterState.lookupLens.put state
      ⟨none, true, none, none⟩)
  rcases unifiedLookup_found (R := UnifiedCleanAfter R)
      w accumulator query value hq m hm hfind
      (unifiedCleanTailProgram returnLabel right) state base with
    ⟨lookupSteps, hbound, hlookup⟩
  have hdiscard := run_lensPhase_to_right
    (discardCoreRenaming .work1) FullInterpreterState.moveLens
    discardProgram .done (by rfl)
    (Sum.inl LookupDecisionLabel.decide)
    (unifiedCleanAfterProgram returnLabel right)
    (discard_correct_from
      (FullInterpreterState.moveLens.get foundState)
      ((fixedBits w query).reverse.map SparseSymbol.bit)) rfl
    foundState (operandResultBase w accumulator value m base)
  simp only [List.length_map, List.length_reverse, fixedBits_length] at hdiscard
  rw [discard_decision_bridge (R := R) foundState
    (operandResultBase w accumulator value m base) (by rfl)] at hdiscard
  have houtcome := lookupDecision_found_step returnLabel right
    (FullInterpreterState.moveLens.put foundState default) (by rfl)
    (operandResultBase w accumulator value m base)
  have houtcome' :
      ((fun o => o.bind (TM2.step
        (unifiedCleanAfterProgram returnLabel right)))^[1])
        (some (cleanDecisionCfg
          (FullInterpreterState.moveLens.put foundState default)
          (operandResultBase w accumulator value m base))) =
      some (mapLabelCfg Sum.inr
        (mapLabelCfg Sum.inr
          (cleanReturnCfg returnLabel
            (FullInterpreterState.moveLens.put foundState default)
            (operandResultBase w accumulator value m base)))) := by
    simpa using houtcome
  have htail := chain_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl LookupDecisionLabel.decide))
    (unifiedCleanAfterProgram returnLabel right) hdiscard houtcome'
  have hchain := chain_liftRightProgram
    (lensMultiPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram lookupExit lookupRecordOutcome)
    (unifiedCleanTailProgram returnLabel right) hlookup htail
  refine ⟨lookupSteps + (w + 2 + 1), ?_, ?_⟩
  · omega
  · simpa [unifiedCleanLookupProgram, foundState] using hchain

theorem unifiedCleanLookup_missing {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? query = none)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step
      (unifiedCleanLookupProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 3 * w + 9])
      (some (lensRenamedCfg lookupCoreRenaming
        FullInterpreterState.lookupLens
        (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        state (operandBoundaryBase w accumulator m base))) =
    some (mapLabelCfg (fun l : UnifiedCleanTail R => Sum.inr l)
      (mapLabelCfg (fun l : UnifiedCleanAfter R => Sum.inr l)
        (mapLabelCfg (fun l : UnifiedCleanFinish R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (phaseReturnCfg zeroWordCoreRenaming
              FullInterpreterState.zeroLens returnLabel
              (zeroWordCfg .done
                ((fixedBits w accumulator).map SparseSymbol.bit) []
                ((fixedBits w 0).reverse.map SparseSymbol.bit))
              (FullInterpreterState.moveLens.put
                (lookupRecordOutcome .missing
                  (FullInterpreterState.lookupLens.put state
                    ⟨none, decide m.isEmpty, none, none⟩)) default)
              (operandBoundaryBase w accumulator m base)))))) := by
  let missingState := lookupRecordOutcome LookupScanLabel.missing
    (FullInterpreterState.lookupLens.put state
      ⟨none, decide m.isEmpty, none, none⟩)
  have hlookup := unifiedLookup_missing (R := UnifiedCleanAfter R)
    w accumulator query hq m hm hmissing
    (unifiedCleanTailProgram returnLabel right) state base
  have hdiscard := run_lensPhase_to_right
    (discardCoreRenaming .work1) FullInterpreterState.moveLens
    discardProgram .done (by rfl)
    (Sum.inl LookupDecisionLabel.decide)
    (unifiedCleanAfterProgram returnLabel right)
    (discard_correct_from
      (FullInterpreterState.moveLens.get missingState)
      ((fixedBits w query).reverse.map SparseSymbol.bit)) rfl
    missingState (operandBoundaryBase w accumulator m base)
  simp only [List.length_map, List.length_reverse, fixedBits_length] at hdiscard
  rw [discard_decision_bridge (R := R) missingState
    (operandBoundaryBase w accumulator m base) (by rfl)] at hdiscard
  have houtcome := lookupDecision_missing_step returnLabel right
    w accumulator m base
    (FullInterpreterState.moveLens.put missingState default) (by rfl)
  have houtcome' :
      ((fun o => o.bind (TM2.step
        (unifiedCleanAfterProgram returnLabel right)))^[1])
        (some (cleanDecisionCfg
          (FullInterpreterState.moveLens.put missingState default)
          (operandBoundaryBase w accumulator m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg (Λx := R) zeroWordCoreRenaming
          FullInterpreterState.zeroLens
          (zeroWordCfgState .fill
            (FullInterpreterState.zeroLens.get
              (FullInterpreterState.moveLens.put missingState default))
            ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          (FullInterpreterState.moveLens.put missingState default)
          (operandBoundaryBase w accumulator m base))) := by
    simpa using houtcome
  have hzero := run_lensPhase_to_right zeroWordCoreRenaming
    FullInterpreterState.zeroLens zeroWordProgram .done (by rfl)
    returnLabel right
    (zeroWord_correct_from
      (FullInterpreterState.zeroLens.get
        (FullInterpreterState.moveLens.put missingState default))
      ((fixedBits w accumulator).map SparseSymbol.bit) []) rfl
    (FullInterpreterState.moveLens.put missingState default)
    (operandBoundaryBase w accumulator m base)
  simp only [List.length_map, fixedBits_length, fixedBits_zero,
    List.map_replicate, List.reverse_replicate, List.append_nil] at hzero
  have hafter := chain_liftRightProgram
    (lookupDecisionProgram returnLabel)
    (unifiedCleanFinishProgram returnLabel right) houtcome' hzero
  have htail := chain_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl LookupDecisionLabel.decide))
    (unifiedCleanAfterProgram returnLabel right) hdiscard hafter
  have hchain := chain_liftRightProgram
    (lensMultiPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram lookupExit lookupRecordOutcome)
    (unifiedCleanTailProgram returnLabel right) hlookup htail
  have htime : m.length * (12 * w + 22) + 3 +
      (w + 2 + (1 + (2 * w + 3))) =
      m.length * (12 * w + 22) + 3 * w + 9 := by omega
  rw [htime] at hchain
  simpa [unifiedCleanLookupProgram, missingState] using hchain

theorem unifiedCleanLookup_missing_clean {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? query = none)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step
      (unifiedCleanLookupProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 3 * w + 9])
      (some (lensRenamedCfg lookupCoreRenaming
        FullInterpreterState.lookupLens
        (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        state (operandBoundaryBase w accumulator m base))) =
    some (mapLabelCfg (fun l : UnifiedCleanTail R => Sum.inr l)
      (mapLabelCfg (fun l : UnifiedCleanAfter R => Sum.inr l)
        (mapLabelCfg (fun l : UnifiedCleanFinish R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel
              (FullInterpreterState.zeroLens.put
                (FullInterpreterState.moveLens.put
                  (lookupRecordOutcome .missing
                    (FullInterpreterState.lookupLens.put state
                      ⟨none, decide m.isEmpty, none, none⟩)) default) default)
              (operandResultBase w accumulator 0 m base)))))) := by
  have h := unifiedCleanLookup_missing w accumulator query hq m hm hmissing
    returnLabel right state base
  have hb := zero_return_bridge returnLabel w accumulator m base
    (FullInterpreterState.moveLens.put
      (lookupRecordOutcome .missing
        (FullInterpreterState.lookupLens.put state
          ⟨none, decide m.isEmpty, none, none⟩)) default)
  have hout := congrArg (fun c => some
    (mapLabelCfg (fun l : UnifiedCleanTail R =>
        (Sum.inr l : UnifiedCleanLookupLabel R))
      (mapLabelCfg (fun l : UnifiedCleanAfter R => Sum.inr l)
        (mapLabelCfg (fun l : UnifiedCleanFinish R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l) c))))) hb
  exact h.trans hout

end Lax20Proofs.RamToTM
