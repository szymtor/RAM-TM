import Lax51Proofs.RamToTM.UnifiedCleanLookup
import Lax51Proofs.RamToTM.BoundedLiteralGlobal
import Lax51Proofs.RamToTM.QueryTransferPipeline

namespace Lax51Proofs.RamToTM

open Turing TM2

inductive LookupInitLabel
  | init
  deriving DecidableEq, Fintype, Inhabited

abbrev DirectOperandTail (R : Type) :=
  Sum LookupInitLabel (UnifiedCleanLookupLabel R)
abbrev DirectOperandLabel (R : Type) :=
  Sum LiteralWordLabel (DirectOperandTail R)

def lookupInitialControl : LookupCellControl :=
  ⟨none, true, none, none⟩

def lookupInitProgram {N : ℕ} {R : Type} :
    LookupInitLabel → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (DirectOperandTail R) (FullInterpreterState N)
  | .init =>
      .load (fun state =>
        FullInterpreterState.lookupLens.put state lookupInitialControl) <|
      .goto fun _ => .inr (Sum.inl LookupScanLabel.scan)

def directOperandTailProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DirectOperandTail R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (DirectOperandTail R) (FullInterpreterState N) :=
  liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right)

def directOperandProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DirectOperandLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (DirectOperandLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft literalQueryCoreRenaming
      FullInterpreterState.literalLens (boundedLiteralWordProgram N)
      .done (Sum.inl LookupInitLabel.init))
    (directOperandTailProgram returnLabel right)

def lookupInitCfg {N : ℕ} {R : Type}
    (state : FullInterpreterState N)
    (tapes : CoreStack → List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (DirectOperandTail R) (FullInterpreterState N) where
  l := some (.inl .init)
  var := state
  stk := tapes

theorem literalQuery_init_bridge {N : ℕ} {R : Type}
    (n : ℕ) (hn : n ≤ N) (w accumulator : ℕ)
    (m : SparseMemory) (base : CoreStack → List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg literalQueryCoreRenaming
      FullInterpreterState.literalLens
      (Sum.inl LookupInitLabel.init : DirectOperandTail R)
      (boundedLiteralWordCfg N .done
        ⟨n / 2 ^ w, by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
        ((fixedBits w accumulator).map SparseSymbol.bit) []
        ((fixedBits w n).reverse.map SparseSymbol.bit))
      state (operandBoundaryBase w accumulator m base) =
    lookupInitCfg (R := R)
      (FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w, by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
      (lookupQueryBase w accumulator (n % 2 ^ w) m base) := by
  simp [phaseReturnCfg, lookupInitCfg, lensRenamedCfg,
    literalQueryCoreRenaming, literalQueryCoreDecode,
    boundedLiteralWordCfg, literalWordStacks,
    operandBoundaryBase, lookupQueryBase, renamedStacks,
    fixedBits_mod_word]
  funext k
  cases k <;> simp [renamedStacks, literalQueryCoreRenaming,
    literalQueryCoreDecode, boundedLiteralWordCfg, literalWordStacks,
    operandBoundaryBase, lookupQueryBase, fixedBits_mod_word,
    List.map_reverse]

theorem lookupInit_step {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol)
    (state : FullInterpreterState N)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    TM2.step (directOperandTailProgram returnLabel right)
      (lookupInitCfg (R := R) state
        (lookupQueryBase w accumulator query m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg lookupCoreRenaming
        FullInterpreterState.lookupLens
        (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        state (operandBoundaryBase w accumulator m base))) := by
  simp [directOperandTailProgram, lookupInitProgram, lookupInitCfg,
    liftRightProgram, TM2.step, mapLabelCfg, lensRenamedCfg,
    lookupScanMacroCfg, lookupScanCfg, lookupScanStacks,
    lookupCoreRenaming, lookupCoreDecode, lookupInitialControl,
    lookupQueryBase, operandBoundaryBase, renamedStacks]
  funext k
  cases k <;> simp [lookupQueryBase, operandBoundaryBase,
    renamedStacks, lookupCoreRenaming, lookupCoreDecode,
    lookupScanMacroCfg, lookupScanCfg, lookupScanStacks,
    List.map_reverse]

theorem directOperand_found {N : ℕ} {R : Type}
    (address : ℕ) (haN : address ≤ N)
    (w accumulator value : ℕ)
    (m : SparseMemory) (hm : m.Normalized w)
    (hfind : m.find? (address % 2 ^ w) = some value)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ∃ steps ≤ m.length * (12 * w + 22) + 14 * w + 30,
      ((fun o => o.bind (TM2.step
        (directOperandProgram returnLabel right)))^[steps])
        (some (lensRenamedCfg literalQueryCoreRenaming
          FullInterpreterState.literalLens
          (boundedLiteralWordCfg N .emit ⟨address, by omega⟩
            ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          state (operandBoundaryBase w accumulator m base))) =
      some (mapLabelCfg (fun l : DirectOperandTail R => Sum.inr l)
        (mapLabelCfg (fun l : UnifiedCleanLookupLabel R => Sum.inr l)
          (mapLabelCfg (fun l : UnifiedCleanTail R => Sum.inr l)
            (mapLabelCfg (fun l : UnifiedCleanAfter R => Sum.inr l)
              (mapLabelCfg (fun l : UnifiedCleanFinish R => Sum.inr l)
                (mapLabelCfg (fun l : R => Sum.inr l)
                  (cleanReturnCfg returnLabel
                    (FullInterpreterState.moveLens.put
                      (lookupRecordOutcome .found
                        (FullInterpreterState.lookupLens.put
                          (FullInterpreterState.literalLens.put state
                            ⟨none, ⟨address / 2 ^ w, by
                              exact lt_of_le_of_lt
                                (Nat.div_le_self _ _) (by omega)⟩⟩)
                          ⟨none, true, none, none⟩)) default)
                    (operandResultBase w accumulator value m base)))))))) := by
  let literalState := FullInterpreterState.literalLens.put state
    ⟨none, ⟨address / 2 ^ w, by
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
  let query := address % 2 ^ w
  have hquery : query < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have hliteral := run_lensPhase_to_right literalQueryCoreRenaming
    FullInterpreterState.literalLens (boundedLiteralWordProgram N)
    .done (by rfl) (Sum.inl LookupInitLabel.init)
    (directOperandTailProgram returnLabel right)
    (boundedLiteralWord_correct_exact N address haN
      ((fixedBits w accumulator).map SparseSymbol.bit) []) rfl
    state (operandBoundaryBase w accumulator m base)
  simp only [List.length_map, fixedBits_length, List.append_nil] at hliteral
  rw [literalQuery_init_bridge (R := R) address haN w accumulator m base
    state] at hliteral
  have hinitStep := lookupInit_step (R := R) w accumulator query m base
    literalState returnLabel right
  have hinit :
      ((fun o => o.bind (TM2.step
        (directOperandTailProgram returnLabel right)))^[1])
        (some (lookupInitCfg (R := R) literalState
          (lookupQueryBase w accumulator query m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg lookupCoreRenaming
          FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          literalState (operandBoundaryBase w accumulator m base))) := by
    simpa using hinitStep
  rcases unifiedCleanLookup_found w accumulator query value hquery m hm hfind
      returnLabel right literalState base with
    ⟨lookupSteps, hbound, hlookup⟩
  have htail := chain_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) hinit hlookup
  have hchain := chain_liftRightProgram
    (lensPhaseLeft literalQueryCoreRenaming
      FullInterpreterState.literalLens (boundedLiteralWordProgram N)
      .done (Sum.inl LookupInitLabel.init))
    (directOperandTailProgram returnLabel right) hliteral htail
  refine ⟨2 * w + 3 + (1 + lookupSteps), ?_, ?_⟩
  · omega
  · simpa [directOperandProgram, literalState, query] using hchain

theorem directOperand_missing {N : ℕ} {R : Type}
    (address : ℕ) (haN : address ≤ N)
    (w accumulator : ℕ)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? (address % 2 ^ w) = none)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step
      (directOperandProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 5 * w + 13])
      (some (lensRenamedCfg literalQueryCoreRenaming
        FullInterpreterState.literalLens
        (boundedLiteralWordCfg N .emit ⟨address, by omega⟩
          ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        state (operandBoundaryBase w accumulator m base))) =
    some (mapLabelCfg (fun l : DirectOperandTail R => Sum.inr l)
      (mapLabelCfg (fun l : UnifiedCleanLookupLabel R => Sum.inr l)
        (mapLabelCfg (fun l : UnifiedCleanTail R => Sum.inr l)
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
                      (FullInterpreterState.lookupLens.put
                        (FullInterpreterState.literalLens.put state
                          ⟨none, ⟨address / 2 ^ w, by
                            exact lt_of_le_of_lt
                              (Nat.div_le_self _ _) (by omega)⟩⟩)
                        ⟨none, decide m.isEmpty, none, none⟩)) default)
                  (operandBoundaryBase w accumulator m base)))))))) := by
  let literalState := FullInterpreterState.literalLens.put state
    ⟨none, ⟨address / 2 ^ w, by
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
  let query := address % 2 ^ w
  have hquery : query < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have hliteral := run_lensPhase_to_right literalQueryCoreRenaming
    FullInterpreterState.literalLens (boundedLiteralWordProgram N)
    .done (by rfl) (Sum.inl LookupInitLabel.init)
    (directOperandTailProgram returnLabel right)
    (boundedLiteralWord_correct_exact N address haN
      ((fixedBits w accumulator).map SparseSymbol.bit) []) rfl
    state (operandBoundaryBase w accumulator m base)
  simp only [List.length_map, fixedBits_length, List.append_nil] at hliteral
  rw [literalQuery_init_bridge (R := R) address haN w accumulator m base
    state] at hliteral
  have hinitStep := lookupInit_step (R := R) w accumulator query m base
    literalState returnLabel right
  have hinit :
      ((fun o => o.bind (TM2.step
        (directOperandTailProgram returnLabel right)))^[1])
        (some (lookupInitCfg (R := R) literalState
          (lookupQueryBase w accumulator query m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg lookupCoreRenaming
          FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          literalState (operandBoundaryBase w accumulator m base))) := by
    simpa using hinitStep
  have hlookup := unifiedCleanLookup_missing w accumulator query hquery
    m hm hmissing returnLabel right literalState base
  have htail := chain_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) hinit hlookup
  have hchain := chain_liftRightProgram
    (lensPhaseLeft literalQueryCoreRenaming
      FullInterpreterState.literalLens (boundedLiteralWordProgram N)
      .done (Sum.inl LookupInitLabel.init))
    (directOperandTailProgram returnLabel right) hliteral htail
  have htime : 2 * w + 3 +
      (1 + (m.length * (12 * w + 22) + 3 * w + 9)) =
      m.length * (12 * w + 22) + 5 * w + 13 := by omega
  rw [htime] at hchain
  simpa [directOperandProgram, literalState, query] using hchain

def embedDirectReturnCfg {N : ℕ} {R : Type}
    (c : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (DirectOperandLabel R) (FullInterpreterState N) :=
  mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr <|
    mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr <|
      mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr c

theorem transport_iterate_direct_right {N : ℕ} {R : Type}
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps : ℕ}
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun : ((fun o => o.bind (TM2.step right))^[steps])
      (some c) = some d) :
    ((fun o => o.bind (TM2.step
      (directOperandProgram returnLabel right)))^[steps])
      (some (embedDirectReturnCfg c)) =
    some (embedDirectReturnCfg d) := by
  have h₁ := transport_iterate_liftRightProgram
    (lensPhaseLeft zeroWordCoreRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done returnLabel) right hrun
  have h₂ := transport_iterate_liftRightProgram
    (lookupDecisionProgram returnLabel)
    (unifiedCleanFinishProgram returnLabel right) h₁
  have h₃ := transport_iterate_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl LookupDecisionLabel.decide))
    (unifiedCleanAfterProgram returnLabel right) h₂
  have h₄ := transport_iterate_liftRightProgram
    (lensMultiPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram lookupExit lookupRecordOutcome)
    (unifiedCleanTailProgram returnLabel right) h₃
  have h₅ := transport_iterate_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) h₄
  have h₆ := transport_iterate_liftRightProgram
    (lensPhaseLeft literalQueryCoreRenaming
      FullInterpreterState.literalLens (boundedLiteralWordProgram N)
      .done (Sum.inl LookupInitLabel.init))
    (directOperandTailProgram returnLabel right) h₅
  simpa [directOperandProgram, directOperandTailProgram,
    unifiedCleanLookupProgram, unifiedLookupProgram,
    unifiedCleanTailProgram, unifiedCleanAfterProgram,
    unifiedCleanFinishProgram, embedDirectReturnCfg] using h₆

theorem directOperandTail_found {N : ℕ} {R : Type}
    (w accumulator query value : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hfind : m.find? query = some value)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ∃ steps ≤ m.length * (12 * w + 22) + 12 * w + 27,
      ((fun o => o.bind (TM2.step
        (directOperandTailProgram returnLabel right)))^[steps])
        (some (lookupInitCfg (R := R) state
          (lookupQueryBase w accumulator query m base))) =
      some (mapLabelCfg (fun l : UnifiedCleanLookupLabel R => Sum.inr l)
        (mapLabelCfg (fun l : UnifiedCleanTail R => Sum.inr l)
          (mapLabelCfg (fun l : UnifiedCleanAfter R => Sum.inr l)
            (mapLabelCfg (fun l : UnifiedCleanFinish R => Sum.inr l)
              (mapLabelCfg (fun l : R => Sum.inr l)
                (cleanReturnCfg returnLabel
                  (FullInterpreterState.moveLens.put
                    (lookupRecordOutcome .found
                      (FullInterpreterState.lookupLens.put state
                        lookupInitialControl)) default)
                  (operandResultBase w accumulator value m base))))))) := by
  have hinitStep := lookupInit_step (R := R) w accumulator query m base
    state returnLabel right
  have hinit :
      ((fun o => o.bind (TM2.step
        (directOperandTailProgram returnLabel right)))^[1])
        (some (lookupInitCfg (R := R) state
          (lookupQueryBase w accumulator query m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg lookupCoreRenaming FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          state (operandBoundaryBase w accumulator m base))) := by
    simpa using hinitStep
  rcases unifiedCleanLookup_found w accumulator query value hq m hm hfind
      returnLabel right state base with ⟨steps, hbound, hlookup⟩
  have hchain := chain_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) hinit hlookup
  refine ⟨1 + steps, by omega, ?_⟩
  simpa [directOperandTailProgram, lookupInitialControl] using hchain

theorem directOperandTail_missing {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? query = none)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step
      (directOperandTailProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 3 * w + 10])
      (some (lookupInitCfg (R := R) state
        (lookupQueryBase w accumulator query m base))) =
    some (mapLabelCfg (fun l : UnifiedCleanLookupLabel R => Sum.inr l)
      (mapLabelCfg (fun l : UnifiedCleanTail R => Sum.inr l)
        (mapLabelCfg (fun l : UnifiedCleanAfter R => Sum.inr l)
          (mapLabelCfg (fun l : UnifiedCleanFinish R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (cleanReturnCfg returnLabel
                (FullInterpreterState.zeroLens.put
                  (FullInterpreterState.moveLens.put
                    (lookupRecordOutcome .missing
                      (FullInterpreterState.lookupLens.put state
                        ⟨none, decide m.isEmpty, none, none⟩)) default) default)
                (operandResultBase w accumulator 0 m base))))))) := by
  have hinitStep := lookupInit_step (R := R) w accumulator query m base
    state returnLabel right
  have hinit :
      ((fun o => o.bind (TM2.step
        (directOperandTailProgram returnLabel right)))^[1])
        (some (lookupInitCfg (R := R) state
          (lookupQueryBase w accumulator query m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg lookupCoreRenaming FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          state (operandBoundaryBase w accumulator m base))) := by
    simpa using hinitStep
  have hlookup := unifiedCleanLookup_missing_clean w accumulator query hq
    m hm hmissing returnLabel right state base
  have hchain := chain_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) hinit hlookup
  have htime : 1 + (m.length * (12 * w + 22) + 3 * w + 9) =
      m.length * (12 * w + 22) + 3 * w + 10 := by omega
  rw [htime] at hchain
  simpa only [directOperandTailProgram, lookupInitialControl] using hchain

theorem directOperand_found_clean {N : ℕ} {R : Type}
    (address : ℕ) (haN : address ≤ N)
    (w accumulator value : ℕ)
    (m : SparseMemory) (hm : m.Normalized w)
    (hfind : m.find? (address % 2 ^ w) = some value)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ∃ steps ≤ m.length * (12 * w + 22) + 14 * w + 30,
      ((fun o => o.bind (TM2.step
        (directOperandProgram returnLabel right)))^[steps])
        (some (lensRenamedCfg literalQueryCoreRenaming
          FullInterpreterState.literalLens
          (boundedLiteralWordCfg N .emit ⟨address, by omega⟩
            ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          state (operandBoundaryBase w accumulator m base))) =
      some (embedDirectReturnCfg
        (cleanReturnCfg returnLabel
          (FullInterpreterState.moveLens.put
            (lookupRecordOutcome .found
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.literalLens.put state
                  ⟨none, ⟨address / 2 ^ w, by
                    exact lt_of_le_of_lt
                      (Nat.div_le_self _ _) (by omega)⟩⟩)
                ⟨none, true, none, none⟩)) default)
          (operandResultBase w accumulator value m base))) := by
  simpa [embedDirectReturnCfg] using directOperand_found address haN w
    accumulator value m hm hfind returnLabel right state base

theorem directOperand_missing_clean {N : ℕ} {R : Type}
    (address : ℕ) (haN : address ≤ N)
    (w accumulator : ℕ)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? (address % 2 ^ w) = none)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step
      (directOperandProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 5 * w + 13])
      (some (lensRenamedCfg literalQueryCoreRenaming
        FullInterpreterState.literalLens
        (boundedLiteralWordCfg N .emit ⟨address, by omega⟩
          ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        state (operandBoundaryBase w accumulator m base))) =
    some (embedDirectReturnCfg
      (cleanReturnCfg returnLabel
        (FullInterpreterState.zeroLens.put
          (FullInterpreterState.moveLens.put
            (lookupRecordOutcome .missing
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.literalLens.put state
                  ⟨none, ⟨address / 2 ^ w, by
                    exact lt_of_le_of_lt
                      (Nat.div_le_self _ _) (by omega)⟩⟩)
                ⟨none, decide m.isEmpty, none, none⟩)) default) default)
        (operandResultBase w accumulator 0 m base))) := by
  have h := directOperand_missing address haN w accumulator m hm hmissing
    returnLabel right state base
  have hb := zero_return_bridge returnLabel w accumulator m base
    (FullInterpreterState.moveLens.put
      (lookupRecordOutcome .missing
        (FullInterpreterState.lookupLens.put
          (FullInterpreterState.literalLens.put state
            ⟨none, ⟨address / 2 ^ w, by
              exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
          ⟨none, decide m.isEmpty, none, none⟩)) default)
  have hout := congrArg (fun c => some (embedDirectReturnCfg c)) hb
  simpa [embedDirectReturnCfg] using h.trans hout

end Lax51Proofs.RamToTM
