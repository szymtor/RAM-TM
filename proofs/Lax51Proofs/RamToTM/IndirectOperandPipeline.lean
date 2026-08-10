import Lax51Proofs.RamToTM.DirectOperandPipeline

namespace Lax51Proofs.RamToTM

open Turing TM2

abbrev IndirectTransferLabel (R : Type) :=
  QueryTransferLabel (DirectOperandTail R)
abbrev IndirectOperandLabel (R : Type) :=
  DirectOperandLabel (IndirectTransferLabel R)

def indirectTransferProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    IndirectTransferLabel R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol)
      (IndirectTransferLabel R) (FullInterpreterState N) :=
  queryTransferProgram (Sum.inl LookupInitLabel.init)
    (directOperandTailProgram returnLabel right)

def indirectOperandProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    IndirectOperandLabel R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol)
      (IndirectOperandLabel R) (FullInterpreterState N) :=
  directOperandProgram (Sum.inl SymbolMoveLabel.loop)
    (indirectTransferProgram returnLabel right)

theorem cleanReturn_queryTransfer_bridge {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol)
    (state : FullInterpreterState N) :
    cleanReturnCfg (Sum.inl SymbolMoveLabel.loop : QueryTransferLabel R)
      state (operandResultBase w accumulator query m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfgState .loop
        (FullInterpreterState.moveLens.get state)
        ((fixedBits w query).reverse.map SparseSymbol.bit) [])
      state (operandResultBase w accumulator query m base) := by
  simp [cleanReturnCfg, lensRenamedCfg, symbolMoveLocalCfgState,
    symbolMoveStacks, symbolMoveCoreRenaming, symbolMoveCoreDecode,
    operandResultBase, renamedStacks]
  constructor
  · rw [FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
      symbolMoveCoreDecode, symbolMoveLocalCfgState, symbolMoveStacks,
      operandResultBase, List.map_reverse]

theorem queryTransfer_init_bridge {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work2 .work1 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl LookupInitLabel.init : DirectOperandTail R)
      (symbolMoveLocalCfg .done []
        ((fixedBits w query).reverse.map SparseSymbol.bit))
      state (lookupQueryBase w accumulator query m base) =
    lookupInitCfg (R := R)
      (FullInterpreterState.moveLens.put state default)
      (lookupQueryBase w accumulator query m base) := by
  simp [phaseReturnCfg, lookupInitCfg, lensRenamedCfg,
    symbolMoveCoreRenaming, symbolMoveCoreDecode,
    symbolMoveLocalCfg, symbolMoveStacks, lookupQueryBase,
    renamedStacks, List.map_reverse]
  funext k
  cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
    lookupQueryBase, List.map_reverse]

theorem transport_iterate_indirectTransfer_right {N : ℕ} {R : Type}
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps : ℕ}
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (DirectOperandTail R) (FullInterpreterState N)}
    (hrun : ((fun o => o.bind (TM2.step
      (directOperandTailProgram returnLabel right)))^[steps])
      (some c) = some d) :
    ((fun o => o.bind (TM2.step
      (indirectTransferProgram returnLabel right)))^[steps])
      (some (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr c))) =
    some (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr d)) := by
  have h₁ := transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work2 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl LookupInitLabel.init))
    (directOperandTailProgram returnLabel right) hrun
  have h₂ := transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (queryTransferTailProgram (Sum.inl LookupInitLabel.init)
      (directOperandTailProgram returnLabel right)) h₁
  simpa [indirectTransferProgram, queryTransferProgram] using h₂

def embedDirectTailReturnCfg {N : ℕ} {R : Type}
    (c : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (DirectOperandTail R) (FullInterpreterState N) :=
  mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr <|
    mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr <|
      mapLabelCfg Sum.inr c

def embedIndirectTransferReturnCfg {N : ℕ} {R : Type}
    (c : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (IndirectTransferLabel R) (FullInterpreterState N) :=
  mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr <|
    embedDirectTailReturnCfg c

def embedIndirectReturnCfg {N : ℕ} {R : Type}
    (c : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (IndirectOperandLabel R) (FullInterpreterState N) :=
  embedDirectReturnCfg (embedIndirectTransferReturnCfg c)

theorem transport_iterate_directTail_right {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps : Nat}
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun : ((fun o => o.bind (TM2.step right))^[steps])
      (some c) = some d) :
    ((fun o => o.bind (TM2.step
      (directOperandTailProgram returnLabel right)))^[steps])
      (some (embedDirectTailReturnCfg c)) =
    some (embedDirectTailReturnCfg d) := by
  have h1 := transport_iterate_liftRightProgram
    (lensPhaseLeft zeroWordCoreRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done returnLabel) right hrun
  have h2 := transport_iterate_liftRightProgram
    (lookupDecisionProgram returnLabel)
    (unifiedCleanFinishProgram returnLabel right) h1
  have h3 := transport_iterate_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl LookupDecisionLabel.decide))
    (unifiedCleanAfterProgram returnLabel right) h2
  have h4 := transport_iterate_liftRightProgram
    (lensMultiPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram lookupExit lookupRecordOutcome)
    (unifiedCleanTailProgram returnLabel right) h3
  have h5 := transport_iterate_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) h4
  simpa [directOperandTailProgram, unifiedCleanLookupProgram,
    unifiedLookupProgram, unifiedCleanTailProgram, unifiedCleanAfterProgram,
    unifiedCleanFinishProgram, embedDirectTailReturnCfg] using h5

theorem transport_iterate_indirect_right {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps : Nat}
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun : ((fun o => o.bind (TM2.step right))^[steps])
      (some c) = some d) :
    ((fun o => o.bind (TM2.step
      (indirectOperandProgram returnLabel right)))^[steps])
      (some (embedIndirectReturnCfg c)) =
    some (embedIndirectReturnCfg d) := by
  have htail := transport_iterate_directTail_right returnLabel right hrun
  have htransfer := transport_iterate_indirectTransfer_right
    returnLabel right htail
  have hall := transport_iterate_direct_right
    (Sum.inl SymbolMoveLabel.loop : IndirectTransferLabel R)
    (indirectTransferProgram returnLabel right) htransfer
  simpa [embedIndirectReturnCfg, embedIndirectTransferReturnCfg] using hall

private theorem chain_iterations {X : Type} (step : X → X)
    {a b c : X} {m n : ℕ}
    (h₁ : (step^[m]) a = b) (h₂ : (step^[n]) b = c) :
    (step^[m + n]) a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]

theorem indirectContinue_found {N : ℕ} {R : Type}
    (w accumulator pointer value : ℕ) (hp : pointer < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hfind : m.find? pointer = some value)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ∃ steps ≤ m.length * (12 * w + 22) + 14 * w + 31,
      ((fun o => o.bind (TM2.step
        (indirectTransferProgram returnLabel right)))^[steps])
        (some (cleanReturnCfg
          (Sum.inl SymbolMoveLabel.loop : IndirectTransferLabel R)
          state (operandResultBase w accumulator pointer m base))) =
      some (embedIndirectTransferReturnCfg
        (cleanReturnCfg returnLabel
          (FullInterpreterState.moveLens.put
            (lookupRecordOutcome .found
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.moveLens.put state default)
                lookupInitialControl)) default)
          (operandResultBase w accumulator value m base))) := by
  have htransfer := queryTransfer_correct (R := DirectOperandTail R)
    w accumulator pointer m (Sum.inl LookupInitLabel.init)
    (directOperandTailProgram returnLabel right) state base
  have hb := queryTransfer_init_bridge (R := R) w accumulator pointer m base
    state
  have hb' := congrArg (fun c => some
    (mapLabelCfg (fun l : QueryTransferTail (DirectOperandTail R) =>
        (Sum.inr l : IndirectTransferLabel R))
      (mapLabelCfg (fun l : DirectOperandTail R => Sum.inr l) c))) hb
  have htransfer' := htransfer.trans hb'
  have htransfer'' :
      ((fun o => o.bind (TM2.step
        (indirectTransferProgram returnLabel right)))^[2 * w + 4])
        (some (cleanReturnCfg
          (Sum.inl SymbolMoveLabel.loop : IndirectTransferLabel R)
          state (operandResultBase w accumulator pointer m base))) =
      some (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr
        (lookupInitCfg (R := R)
          (FullInterpreterState.moveLens.put state default)
          (lookupQueryBase w accumulator pointer m base)))) := by
    rw [cleanReturn_queryTransfer_bridge (R := DirectOperandTail R)
      w accumulator pointer m base state]
    exact htransfer'
  rcases directOperandTail_found w accumulator pointer value hp m hm hfind
      returnLabel right (FullInterpreterState.moveLens.put state default) base with
    ⟨lookupSteps, hbound, hlookup⟩
  have hlift := transport_iterate_indirectTransfer_right returnLabel right hlookup
  have hchain := chain_iterations
    (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (IndirectTransferLabel R) (FullInterpreterState N)) =>
      o.bind (TM2.step (indirectTransferProgram returnLabel right)))
    htransfer'' hlift
  refine ⟨2 * w + 4 + lookupSteps, by omega, ?_⟩
  simpa [embedIndirectTransferReturnCfg, embedDirectTailReturnCfg,
    lookupInitialControl] using hchain

theorem indirectContinue_missing {N : ℕ} {R : Type}
    (w accumulator pointer : ℕ) (hp : pointer < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? pointer = none)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step
      (indirectTransferProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 5 * w + 14])
      (some (cleanReturnCfg
        (Sum.inl SymbolMoveLabel.loop : IndirectTransferLabel R)
        state (operandResultBase w accumulator pointer m base))) =
    some (embedIndirectTransferReturnCfg
      (cleanReturnCfg returnLabel
        (FullInterpreterState.zeroLens.put
          (FullInterpreterState.moveLens.put
            (lookupRecordOutcome .missing
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.moveLens.put state default)
                ⟨none, decide m.isEmpty, none, none⟩)) default) default)
        (operandResultBase w accumulator 0 m base))) := by
  have htransfer := queryTransfer_correct (R := DirectOperandTail R)
    w accumulator pointer m (Sum.inl LookupInitLabel.init)
    (directOperandTailProgram returnLabel right) state base
  have hb := queryTransfer_init_bridge (R := R) w accumulator pointer m base
    state
  have hb' := congrArg (fun c => some
    (mapLabelCfg (fun l : QueryTransferTail (DirectOperandTail R) =>
        (Sum.inr l : IndirectTransferLabel R))
      (mapLabelCfg (fun l : DirectOperandTail R => Sum.inr l) c))) hb
  have htransfer' := htransfer.trans hb'
  have htransfer'' :
      ((fun o => o.bind (TM2.step
        (indirectTransferProgram returnLabel right)))^[2 * w + 4])
        (some (cleanReturnCfg
          (Sum.inl SymbolMoveLabel.loop : IndirectTransferLabel R)
          state (operandResultBase w accumulator pointer m base))) =
      some (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr
        (lookupInitCfg (R := R)
          (FullInterpreterState.moveLens.put state default)
          (lookupQueryBase w accumulator pointer m base)))) := by
    rw [cleanReturn_queryTransfer_bridge (R := DirectOperandTail R)
      w accumulator pointer m base state]
    exact htransfer'
  have hlookup := directOperandTail_missing w accumulator pointer hp m hm hmissing
    returnLabel right (FullInterpreterState.moveLens.put state default) base
  have hlift := transport_iterate_indirectTransfer_right returnLabel right hlookup
  have hchain := chain_iterations
    (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (IndirectTransferLabel R) (FullInterpreterState N)) =>
      o.bind (TM2.step (indirectTransferProgram returnLabel right)))
    htransfer'' hlift
  have htime : 2 * w + 4 +
      (m.length * (12 * w + 22) + 3 * w + 10) =
      m.length * (12 * w + 22) + 5 * w + 14 := by omega
  rw [htime] at hchain
  simpa [embedIndirectTransferReturnCfg, embedDirectTailReturnCfg] using hchain

theorem indirectOperand_correct {N : ℕ} {R : Type}
    (address : ℕ) (haN : address ≤ N)
    (w accumulator : ℕ) (m : SparseMemory) (hm : m.Normalized w)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ∃ steps ≤ 2 * (m.length * (12 * w + 22)) + 28 * w + 61,
      ∃ finalState : FullInterpreterState N,
      ((fun o => o.bind (TM2.step
        (indirectOperandProgram returnLabel right)))^[steps])
        (some (lensRenamedCfg literalQueryCoreRenaming
          FullInterpreterState.literalLens
          (boundedLiteralWordCfg N .emit ⟨address, by omega⟩
            ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          state (operandBoundaryBase w accumulator m base))) =
      some (embedIndirectReturnCfg
        (cleanReturnCfg returnLabel finalState
          (operandResultBase w accumulator
            (m.read (m.read (address % 2 ^ w))) m base))) := by
  let query := address % 2 ^ w
  have hquery : query < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  cases hfirst : m.find? query with
  | none =>
      have hreadFirst : m.read query = 0 := by
        have h := SparseMemory.find?_getD m query
        rw [hfirst] at h
        exact h.symm
      let state₁ := FullInterpreterState.zeroLens.put
        (FullInterpreterState.moveLens.put
          (lookupRecordOutcome LookupScanLabel.missing
            (FullInterpreterState.lookupLens.put
              (FullInterpreterState.literalLens.put state
                ⟨none, ⟨address / 2 ^ w, by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
              ⟨none, decide m.isEmpty, none, none⟩)) default) default
      have hrunFirst := directOperand_missing_clean
        (R := IndirectTransferLabel R) address haN w accumulator m hm hfirst
        (Sum.inl SymbolMoveLabel.loop)
        (indirectTransferProgram returnLabel right) state base
      cases hsecond : m.find? 0 with
      | none =>
          have hreadSecond : m.read 0 = 0 := by
            have h := SparseMemory.find?_getD m 0
            rw [hsecond] at h
            exact h.symm
          have hcont := indirectContinue_missing w accumulator 0
            (Nat.two_pow_pos w) m hm hsecond returnLabel right state₁ base
          have hlift := transport_iterate_direct_right
            (Sum.inl SymbolMoveLabel.loop : IndirectTransferLabel R)
            (indirectTransferProgram returnLabel right) hcont
          have hchain := chain_iterations
            (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
                (IndirectOperandLabel R) (FullInterpreterState N)) =>
              o.bind (TM2.step (indirectOperandProgram returnLabel right)))
            hrunFirst hlift
          let finalState := FullInterpreterState.zeroLens.put
            (FullInterpreterState.moveLens.put
              (lookupRecordOutcome LookupScanLabel.missing
                (FullInterpreterState.lookupLens.put
                  (FullInterpreterState.moveLens.put state₁ default)
                  ⟨none, decide m.isEmpty, none, none⟩)) default) default
          refine ⟨m.length * (12 * w + 22) + 5 * w + 13 +
              (m.length * (12 * w + 22) + 5 * w + 14), by omega,
            finalState, ?_⟩
          simpa [indirectOperandProgram, embedIndirectReturnCfg,
            hreadFirst, hreadSecond, query, state₁, finalState] using hchain
      | some value =>
          have hreadSecond : m.read 0 = value := by
            have h := SparseMemory.find?_getD m 0
            rw [hsecond] at h
            exact h.symm
          have hcont := indirectContinue_found w accumulator 0 value
            (Nat.two_pow_pos w) m hm hsecond returnLabel right state₁ base
          rcases hcont with ⟨contSteps, hcontBound, hcontRun⟩
          have hlift := transport_iterate_direct_right
            (Sum.inl SymbolMoveLabel.loop : IndirectTransferLabel R)
            (indirectTransferProgram returnLabel right) hcontRun
          have hchain := chain_iterations
            (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
                (IndirectOperandLabel R) (FullInterpreterState N)) =>
              o.bind (TM2.step (indirectOperandProgram returnLabel right)))
            hrunFirst hlift
          let finalState := FullInterpreterState.moveLens.put
            (lookupRecordOutcome LookupScanLabel.found
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.moveLens.put state₁ default)
                lookupInitialControl)) default
          refine ⟨m.length * (12 * w + 22) + 5 * w + 13 + contSteps,
            by omega, finalState, ?_⟩
          simpa [indirectOperandProgram, embedIndirectReturnCfg,
            hreadFirst, hreadSecond, query, state₁, finalState,
            lookupInitialControl] using hchain
  | some pointer =>
      have hreadFirst : m.read query = pointer := by
        have h := SparseMemory.find?_getD m query
        rw [hfirst] at h
        exact h.symm
      have hp : pointer < 2 ^ w := by
        rw [← hreadFirst]
        exact SparseMemory.read_lt_of_normalized hm query
      let state₁ := FullInterpreterState.moveLens.put
        (lookupRecordOutcome LookupScanLabel.found
          (FullInterpreterState.lookupLens.put
            (FullInterpreterState.literalLens.put state
              ⟨none, ⟨address / 2 ^ w, by
                exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
            lookupInitialControl)) default
      rcases directOperand_found_clean
          (R := IndirectTransferLabel R) address haN w accumulator pointer m hm
          hfirst (Sum.inl SymbolMoveLabel.loop)
          (indirectTransferProgram returnLabel right) state base with
        ⟨firstSteps, hfirstBound, hrunFirst⟩
      cases hsecond : m.find? pointer with
      | none =>
          have hreadSecond : m.read pointer = 0 := by
            have h := SparseMemory.find?_getD m pointer
            rw [hsecond] at h
            exact h.symm
          have hcont := indirectContinue_missing w accumulator pointer hp
            m hm hsecond returnLabel right state₁ base
          have hlift := transport_iterate_direct_right
            (Sum.inl SymbolMoveLabel.loop : IndirectTransferLabel R)
            (indirectTransferProgram returnLabel right) hcont
          have hchain := chain_iterations
            (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
                (IndirectOperandLabel R) (FullInterpreterState N)) =>
              o.bind (TM2.step (indirectOperandProgram returnLabel right)))
            hrunFirst hlift
          let finalState := FullInterpreterState.zeroLens.put
            (FullInterpreterState.moveLens.put
              (lookupRecordOutcome LookupScanLabel.missing
                (FullInterpreterState.lookupLens.put
                  (FullInterpreterState.moveLens.put state₁ default)
                  ⟨none, decide m.isEmpty, none, none⟩)) default) default
          refine ⟨firstSteps +
              (m.length * (12 * w + 22) + 5 * w + 14), by omega,
            finalState, ?_⟩
          simpa [indirectOperandProgram, embedIndirectReturnCfg,
            hreadFirst, hreadSecond, query, state₁, finalState,
            lookupInitialControl] using hchain
      | some value =>
          have hreadSecond : m.read pointer = value := by
            have h := SparseMemory.find?_getD m pointer
            rw [hsecond] at h
            exact h.symm
          rcases indirectContinue_found w accumulator pointer value hp
              m hm hsecond returnLabel right state₁ base with
            ⟨contSteps, hcontBound, hcontRun⟩
          have hlift := transport_iterate_direct_right
            (Sum.inl SymbolMoveLabel.loop : IndirectTransferLabel R)
            (indirectTransferProgram returnLabel right) hcontRun
          have hchain := chain_iterations
            (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
                (IndirectOperandLabel R) (FullInterpreterState N)) =>
              o.bind (TM2.step (indirectOperandProgram returnLabel right)))
            hrunFirst hlift
          let finalState := FullInterpreterState.moveLens.put
            (lookupRecordOutcome LookupScanLabel.found
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.moveLens.put state₁ default)
                lookupInitialControl)) default
          refine ⟨firstSteps + contSteps, by omega, finalState, ?_⟩
          simpa [indirectOperandProgram, embedIndirectReturnCfg,
            hreadFirst, hreadSecond, query, state₁, finalState,
            lookupInitialControl] using hchain

end Lax51Proofs.RamToTM
