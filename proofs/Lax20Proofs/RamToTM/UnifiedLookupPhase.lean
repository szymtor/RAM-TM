import Lax20Proofs.RamToTM.MultiExitPhase
import Lax20Proofs.RamToTM.CleanLookupPipeline

namespace Lax20Proofs.RamToTM

open Turing TM2

abbrev UnifiedLookupTail (R : Type) := Sum DiscardLabel R
abbrev UnifiedLookupLabel (R : Type) :=
  Sum LookupScanLabel (UnifiedLookupTail R)

def lookupExit {R : Type} : LookupScanLabel → Option (UnifiedLookupTail R)
  | .found | .missing => some (Sum.inl DiscardLabel.loop)
  | _ => none

def lookupRecordOutcome {N : ℕ} (label : LookupScanLabel)
    (state : FullInterpreterState N) : FullInterpreterState N :=
  { state with lookupFound := decide (label = .found) }

theorem lookupExit_halts {R : Type} (label : LookupScanLabel)
    (h : (lookupExit (R := R) label).isSome) :
    lookupScanProgram label = .halt := by
  cases label <;> simp [lookupExit, lookupScanProgram, lookupScanMachine] at h ⊢

def unifiedLookupProgram {N : ℕ} {R : Type}
    (right : UnifiedLookupTail R →
      TM2.Stmt (fun _ : CoreStack => SparseSymbol)
        (UnifiedLookupTail R) (FullInterpreterState N)) :
    UnifiedLookupLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (UnifiedLookupLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensMultiPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram lookupExit lookupRecordOutcome)
    right

theorem unifiedLookup_found_bridge {N : ℕ} {R : Type}
    (w accumulator query value : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol)
    (state : FullInterpreterState N) :
    multiPhaseReturnCfg lookupCoreRenaming FullInterpreterState.lookupLens
      (Sum.inl DiscardLabel.loop : UnifiedLookupTail R)
      (lookupRecordOutcome LookupScanLabel.found)
      (lookupScanMacroCfg .found true
        (encodeSparseMemory w m ++ [.memoryEnd]) []
        ((fixedBits w value).reverse.map SparseSymbol.bit) []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
      state (operandBoundaryBase w accumulator m base) =
    lensRenamedCfg (Λx := R) (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (discardCfgState .loop
        (FullInterpreterState.moveLens.get
          (lookupRecordOutcome .found
            (FullInterpreterState.lookupLens.put state
              ⟨none, true, none, none⟩)))
        ((fixedBits w query).reverse.map SparseSymbol.bit))
      (lookupRecordOutcome .found
        (FullInterpreterState.lookupLens.put state
          ⟨none, true, none, none⟩))
      (operandResultBase w accumulator value m base) := by
  simp [multiPhaseReturnCfg, lensRenamedCfg, lookupRecordOutcome,
    operandBoundaryBase, operandResultBase, renamedStacks,
    lookupCoreRenaming, lookupCoreDecode, lookupScanMacroCfg,
    lookupScanCfg, lookupScanStacks, discardCoreRenaming,
    discardCfgState, discardStacks]
  constructor
  · rw [FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [renamedStacks, lookupCoreRenaming, lookupCoreDecode,
      lookupScanMacroCfg, lookupScanCfg, lookupScanStacks,
      discardCoreRenaming, discardCfgState, discardStacks,
      operandBoundaryBase, operandResultBase, List.map_reverse]

theorem unifiedLookup_missing_bridge {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol)
    (state : FullInterpreterState N) :
    multiPhaseReturnCfg lookupCoreRenaming FullInterpreterState.lookupLens
      (Sum.inl DiscardLabel.loop : UnifiedLookupTail R)
      (lookupRecordOutcome LookupScanLabel.missing)
      (lookupScanMacroCfg .missing (decide m.isEmpty)
        (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
      state (operandBoundaryBase w accumulator m base) =
    lensRenamedCfg (Λx := R) (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (discardCfgState .loop
        (FullInterpreterState.moveLens.get
          (lookupRecordOutcome .missing
            (FullInterpreterState.lookupLens.put state
              ⟨none, decide m.isEmpty, none, none⟩)))
        ((fixedBits w query).reverse.map SparseSymbol.bit))
      (lookupRecordOutcome .missing
        (FullInterpreterState.lookupLens.put state
          ⟨none, decide m.isEmpty, none, none⟩))
      (operandBoundaryBase w accumulator m base) := by
  simp [multiPhaseReturnCfg, lensRenamedCfg, lookupRecordOutcome,
    operandBoundaryBase, renamedStacks, lookupCoreRenaming, lookupCoreDecode,
    lookupScanMacroCfg, lookupScanCfg, lookupScanStacks,
    discardCoreRenaming, discardCfgState, discardStacks]
  constructor
  · rw [FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [renamedStacks, lookupCoreRenaming, lookupCoreDecode,
      lookupScanMacroCfg, lookupScanCfg, lookupScanStacks,
      discardCoreRenaming, discardCfgState, discardStacks,
      operandBoundaryBase, List.map_reverse]

theorem unifiedLookup_found {N : ℕ} {R : Type}
    (w accumulator query value : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hfind : m.find? query = some value)
    (right : UnifiedLookupTail R →
      TM2.Stmt (fun _ : CoreStack => SparseSymbol)
        (UnifiedLookupTail R) (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ∃ steps ≤ m.length * (12 * w + 22) + 11 * w + 23,
      ((fun o => o.bind (TM2.step (unifiedLookupProgram right)))^[steps])
        (some (lensRenamedCfg lookupCoreRenaming
          FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          state (operandBoundaryBase w accumulator m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg (Λx := R) (discardCoreRenaming .work1)
          FullInterpreterState.moveLens
          (discardCfgState .loop
            (FullInterpreterState.moveLens.get
              (lookupRecordOutcome .found
                (FullInterpreterState.lookupLens.put state
                  ⟨none, true, none, none⟩)))
            ((fixedBits w query).reverse.map SparseSymbol.bit))
          (lookupRecordOutcome .found
            (FullInterpreterState.lookupLens.put state
              ⟨none, true, none, none⟩))
          (operandResultBase w accumulator value m base))) := by
  rcases lookupScan_found w query value hq m hm hfind [] with
    ⟨steps, hbound, hrun⟩
  simp only [List.length_nil, Nat.add_zero] at hbound
  refine ⟨steps + 1, by omega, ?_⟩
  have h := run_lensMultiPhase_to_right lookupCoreRenaming
    FullInterpreterState.lookupLens lookupScanProgram lookupExit
    lookupRecordOutcome lookupExit_halts right hrun rfl (by rfl)
    state (operandBoundaryBase w accumulator m base)
  simp only [List.reverse_nil, List.nil_append, lookupScanMacroCfg,
    lookupScanCfg] at h
  have hb := unifiedLookup_found_bridge (R := R) w accumulator query value m
    base state
  simp only [lookupScanMacroCfg, lookupScanCfg] at hb
  have hout := congrArg (fun c => some (mapLabelCfg
    (fun l : UnifiedLookupTail R =>
      (Sum.inr l : UnifiedLookupLabel R)) c)) hb
  simpa [unifiedLookupProgram, lookupScanMacroCfg, lookupScanCfg] using
    h.trans hout

theorem unifiedLookup_missing {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? query = none)
    (right : UnifiedLookupTail R →
      TM2.Stmt (fun _ : CoreStack => SparseSymbol)
        (UnifiedLookupTail R) (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (unifiedLookupProgram right)))^[
      m.length * (12 * w + 22) + 3])
      (some (lensRenamedCfg lookupCoreRenaming
        FullInterpreterState.lookupLens
        (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        state (operandBoundaryBase w accumulator m base))) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg (Λx := R) (discardCoreRenaming .work1)
        FullInterpreterState.moveLens
        (discardCfgState .loop
          (FullInterpreterState.moveLens.get
            (lookupRecordOutcome .missing
              (FullInterpreterState.lookupLens.put state
                ⟨none, decide m.isEmpty, none, none⟩)))
          ((fixedBits w query).reverse.map SparseSymbol.bit))
        (lookupRecordOutcome .missing
          (FullInterpreterState.lookupLens.put state
            ⟨none, decide m.isEmpty, none, none⟩))
        (operandBoundaryBase w accumulator m base))) := by
  have hrun :
      ((fun o : Option
          (TM2.Cfg (fun _ : LookupScanStack => SparseSymbol)
            LookupScanLabel LookupCellControl) =>
        o.bind (TM2.step lookupScanProgram))^[
          m.length * (12 * w + 22) + 2])
        (some (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])) =
      some (lookupScanMacroCfg .missing (decide m.isEmpty)
        (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] []) := by
    simpa [lookupScanProgram, lookupScanMacroCfg, lookupScanCfg,
      lookupScanMachine] using
      lookupScan_all_missing w query hq m hm hmissing true []
  have h := run_lensMultiPhase_to_right lookupCoreRenaming
    FullInterpreterState.lookupLens lookupScanProgram lookupExit
    lookupRecordOutcome lookupExit_halts right hrun rfl (by rfl)
    state (operandBoundaryBase w accumulator m base)
  simp only [lookupScanMacroCfg, lookupScanCfg] at h
  have hb := unifiedLookup_missing_bridge (R := R) w accumulator query m
    base state
  simp only [lookupScanMacroCfg, lookupScanCfg] at hb
  have hout := congrArg (fun c => some (mapLabelCfg
    (fun l : UnifiedLookupTail R =>
      (Sum.inr l : UnifiedLookupLabel R)) c)) hb
  simpa [unifiedLookupProgram, lookupScanMacroCfg, lookupScanCfg] using
    h.trans hout

end Lax20Proofs.RamToTM
