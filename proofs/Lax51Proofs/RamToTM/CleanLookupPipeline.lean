import Lax51Proofs.RamToTM.DiscardStackMacro
import Lax51Proofs.RamToTM.FullLookupExecutions

namespace Lax51Proofs.RamToTM

open Turing TM2

/-! Lookup plus cleanup, expressed as composable global phases.  The input
query is on `work1`; the successful result is returned reversed on `work0`,
and every other work tape is empty. -/

def operandBoundaryBase (w accumulator : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def operandResultBase (w accumulator value : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 => (fixedBits w value).reverse.map SparseSymbol.bit
  | .work1 | .work2 | .work3 | .work4
  | .work5 | .work6 | .work7 => []
  | k => base k

@[simp] theorem operandBoundaryBase_coreStacks (w value : Nat)
    (s : SparseState) :
    operandBoundaryBase w value s.mem (coreStacks w s) =
      coreStacks w { s with acc := value } := by
  funext k
  cases k <;> rfl

abbrev LookupFoundTail (R : Type) := Sum DiscardLabel R
abbrev LookupFoundPipelineLabel (R : Type) :=
  Sum LookupScanLabel (LookupFoundTail R)

def lookupFoundTailProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    LookupFoundTail R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (LookupFoundTail R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done returnLabel)
    right

def lookupFoundPipelineProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    LookupFoundPipelineLabel R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol)
      (LookupFoundPipelineLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram .found (Sum.inl DiscardLabel.loop))
    (lookupFoundTailProgram returnLabel right)

theorem lookupFound_discard_bridge {N : ℕ} {R : Type}
    (w accumulator query value : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol)
    (ambientState : FullInterpreterState N) :
    lensReturnCfg lookupCoreRenaming FullInterpreterState.lookupLens
      (Sum.inl DiscardLabel.loop : LookupFoundTail R)
      (lookupScanMacroCfg .found true
        (encodeSparseMemory w m ++ [.memoryEnd]) []
        ((fixedBits w value).reverse.map SparseSymbol.bit) []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
      ambientState (operandBoundaryBase w accumulator m base) =
    mapLabelCfg Sum.inr
      (lensRenamedCfg (Λx := R) (discardCoreRenaming .work1)
        FullInterpreterState.moveLens
        (discardCfgState .loop
          (FullInterpreterState.moveLens.get
            (FullInterpreterState.lookupLens.put ambientState
              ⟨none, true, none, none⟩))
          ((fixedBits w query).reverse.map SparseSymbol.bit))
        (FullInterpreterState.lookupLens.put ambientState
          ⟨none, true, none, none⟩)
        (operandResultBase w accumulator value m base)) := by
  simp [lensReturnCfg, mapLabelCfg, lensRenamedCfg, operandBoundaryBase,
    operandResultBase, renamedStacks, lookupCoreRenaming, lookupCoreDecode,
    lookupScanMacroCfg, lookupScanCfg, lookupScanStacks,
    discardCoreRenaming, discardCfg, discardCfgState, discardStacks]
  constructor
  · rw [FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [renamedStacks, lookupCoreRenaming, lookupCoreDecode,
      lookupScanMacroCfg, lookupScanCfg, lookupScanStacks,
      discardCoreRenaming, discardCfgState, discardStacks,
      operandBoundaryBase, operandResultBase, List.map_reverse]

theorem lookupFoundPipeline_correct {N : ℕ} {R : Type}
    (w accumulator query value : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hfind : m.find? query = some value)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (ambientState : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ∃ steps ≤ m.length * (12 * w + 22) + 12 * w + 25,
      ((fun o => o.bind (TM2.step
        (lookupFoundPipelineProgram returnLabel right)))^[steps])
        (some (lensRenamedCfg lookupCoreRenaming
          FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          ambientState (operandBoundaryBase w accumulator m base))) =
      some (mapLabelCfg (fun l : LookupFoundTail R => Sum.inr l)
        (mapLabelCfg (fun l : R => Sum.inr l)
          (phaseReturnCfg (discardCoreRenaming .work1)
            FullInterpreterState.moveLens returnLabel
            (discardCfg .done [])
            (FullInterpreterState.lookupLens.put ambientState
              ⟨none, true, none, none⟩)
            (operandResultBase w accumulator value m base)))) := by
  rcases fullLookup_found w query value hq m hm hfind []
      (Sum.inl DiscardLabel.loop)
      (fun label => mapLabelStmt Sum.inr
        (lookupFoundTailProgram returnLabel right label))
      ambientState (operandBoundaryBase w accumulator m base) with
    ⟨lookupSteps, hbound, hlookup⟩
  simp only [List.length_nil, Nat.add_zero] at hbound
  simp only [List.reverse_nil, List.nil_append] at hlookup
  rw [lookupFound_discard_bridge (R := R) w accumulator query value m base
    ambientState] at hlookup
  have hdiscard := run_lensPhase_to_right
    (discardCoreRenaming .work1) FullInterpreterState.moveLens
    discardProgram .done (by rfl) returnLabel right
    (discard_correct_from
      (FullInterpreterState.moveLens.get
        (FullInterpreterState.lookupLens.put ambientState
          ⟨none, true, none, none⟩))
      ((fixedBits w query).reverse.map SparseSymbol.bit)) rfl
    (FullInterpreterState.lookupLens.put ambientState
      ⟨none, true, none, none⟩)
    (operandResultBase w accumulator value m base)
  simp only [List.length_map, List.length_reverse, fixedBits_length] at hdiscard
  have hchain := chain_liftRightProgram
    (lensPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram .found (Sum.inl DiscardLabel.loop))
    (lookupFoundTailProgram returnLabel right) hlookup hdiscard
  refine ⟨lookupSteps + 1 + (w + 2), ?_, ?_⟩
  · omega
  · simpa [lookupFoundPipelineProgram] using hchain

abbrev LookupMissingFinish (R : Type) := Sum ZeroWordLabel R
abbrev LookupMissingTail (R : Type) :=
  Sum DiscardLabel (LookupMissingFinish R)
abbrev LookupMissingPipelineLabel (R : Type) :=
  Sum LookupScanLabel (LookupMissingTail R)

def lookupMissingFinishProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    LookupMissingFinish R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (LookupMissingFinish R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft zeroWordCoreRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done returnLabel)
    right

def lookupMissingTailProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    LookupMissingTail R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (LookupMissingTail R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (lookupMissingFinishProgram returnLabel right)

def lookupMissingPipelineProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    LookupMissingPipelineLabel R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol)
      (LookupMissingPipelineLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram .missing (Sum.inl DiscardLabel.loop))
    (lookupMissingTailProgram returnLabel right)

theorem lookupMissing_discard_bridge {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol)
    (ambientState : FullInterpreterState N) :
    lensReturnCfg lookupCoreRenaming FullInterpreterState.lookupLens
      (Sum.inl DiscardLabel.loop : LookupMissingTail R)
      (lookupScanMacroCfg .missing (decide m.isEmpty)
        (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
      ambientState (operandBoundaryBase w accumulator m base) =
    mapLabelCfg Sum.inr
      (lensRenamedCfg (Λx := LookupMissingFinish R)
        (discardCoreRenaming .work1) FullInterpreterState.moveLens
        (discardCfgState .loop
          (FullInterpreterState.moveLens.get
            (FullInterpreterState.lookupLens.put ambientState
              ⟨none, decide m.isEmpty, none, none⟩))
          ((fixedBits w query).reverse.map SparseSymbol.bit))
        (FullInterpreterState.lookupLens.put ambientState
          ⟨none, decide m.isEmpty, none, none⟩)
        (operandBoundaryBase w accumulator m base)) := by
  simp [lensReturnCfg, mapLabelCfg, lensRenamedCfg, operandBoundaryBase,
    renamedStacks, lookupCoreRenaming, lookupCoreDecode,
    lookupScanMacroCfg, lookupScanCfg, lookupScanStacks,
    discardCoreRenaming, discardCfgState, discardStacks]
  constructor
  · rw [FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [renamedStacks, lookupCoreRenaming, lookupCoreDecode,
      lookupScanMacroCfg, lookupScanCfg, lookupScanStacks,
      discardCoreRenaming, discardCfgState, discardStacks,
      operandBoundaryBase, List.map_reverse]

theorem discard_zero_bridge {N : ℕ} {R : Type}
    (w accumulator : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (Sum.inl ZeroWordLabel.fill : LookupMissingFinish R)
      (discardCfg .done []) state
      (operandBoundaryBase w accumulator m base) =
    lensRenamedCfg (Λx := R) zeroWordCoreRenaming
      FullInterpreterState.zeroLens
      (zeroWordCfgState .fill
        (FullInterpreterState.zeroLens.get
          (FullInterpreterState.moveLens.put state default))
        ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
      (FullInterpreterState.moveLens.put state default)
      (operandBoundaryBase w accumulator m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, operandBoundaryBase,
    renamedStacks, discardCoreRenaming, discardCfg, discardStacks,
    zeroWordCoreRenaming, zeroWordCoreDecode, zeroWordCfgState,
    zeroWordStacks]
  constructor
  · rw [FullInterpreterState.zeroLens.put_get]
  · funext k
    cases k <;> rfl

theorem lookupMissingPipeline_correct {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? query = none)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (ambientState : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step
      (lookupMissingPipelineProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 3 * w + 8])
      (some (lensRenamedCfg lookupCoreRenaming
        FullInterpreterState.lookupLens
        (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        ambientState (operandBoundaryBase w accumulator m base))) =
    some (mapLabelCfg (fun l : LookupMissingTail R => Sum.inr l)
      (mapLabelCfg (fun l : LookupMissingFinish R => Sum.inr l)
        (mapLabelCfg (fun l : R => Sum.inr l)
          (phaseReturnCfg zeroWordCoreRenaming
            FullInterpreterState.zeroLens returnLabel
            (zeroWordCfg .done
              ((fixedBits w accumulator).map SparseSymbol.bit) []
              ((fixedBits w 0).reverse.map SparseSymbol.bit))
            (FullInterpreterState.moveLens.put
              (FullInterpreterState.lookupLens.put ambientState
                ⟨none, decide m.isEmpty, none, none⟩) default)
            (operandBoundaryBase w accumulator m base))))) := by
  let lookupState := FullInterpreterState.lookupLens.put ambientState
    ⟨none, decide m.isEmpty, none, none⟩
  have hlookup := fullLookup_missing w query hq m hm hmissing []
    (Sum.inl DiscardLabel.loop)
    (fun label => mapLabelStmt Sum.inr
      (lookupMissingTailProgram returnLabel right label))
    ambientState (operandBoundaryBase w accumulator m base)
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil,
    List.nil_append] at hlookup
  rw [lookupMissing_discard_bridge (R := R) w accumulator query m base
    ambientState] at hlookup
  have hdiscard := run_lensPhase_to_right
    (discardCoreRenaming .work1) FullInterpreterState.moveLens
    discardProgram .done (by rfl) (Sum.inl ZeroWordLabel.fill)
    (lookupMissingFinishProgram returnLabel right)
    (discard_correct_from
      (FullInterpreterState.moveLens.get lookupState)
      ((fixedBits w query).reverse.map SparseSymbol.bit)) rfl
    lookupState (operandBoundaryBase w accumulator m base)
  simp only [List.length_map, List.length_reverse, fixedBits_length] at hdiscard
  rw [discard_zero_bridge (R := R) w accumulator m base lookupState] at hdiscard
  have hzero := run_lensPhase_to_right zeroWordCoreRenaming
    FullInterpreterState.zeroLens zeroWordProgram .done (by rfl)
    returnLabel right
    (zeroWord_correct_from
      (FullInterpreterState.zeroLens.get
        (FullInterpreterState.moveLens.put lookupState default))
      ((fixedBits w accumulator).map SparseSymbol.bit) []) rfl
    (FullInterpreterState.moveLens.put lookupState default)
    (operandBoundaryBase w accumulator m base)
  simp only [List.length_map, fixedBits_length,
    fixedBits_zero, List.map_replicate, List.reverse_replicate,
    List.append_nil] at hzero
  have htail := chain_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (lookupMissingFinishProgram returnLabel right) hdiscard hzero
  have hchain := chain_liftRightProgram
    (lensPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram .missing (Sum.inl DiscardLabel.loop))
    (lookupMissingTailProgram returnLabel right) hlookup htail
  have htime : m.length * (12 * w + 22) + 3 +
      (w + 1 + 1 + (2 * w + 2 + 1)) =
      m.length * (12 * w + 22) + 3 * w + 8 := by omega
  rw [htime] at hchain
  simpa [lookupMissingPipelineProgram, lookupState] using hchain

end Lax51Proofs.RamToTM
