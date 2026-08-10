import Lax51Proofs.RamToTM.FullDivideCleanup

namespace Lax51Proofs.RamToTM

open Turing TM2

theorem fixedBits_succ_of_lt (w n : Nat) (h : n < 2 ^ w) :
    fixedBits (w + 1) n = fixedBits w n ++ [false] := by
  apply bitsValue_injective_of_length
  · simp
  · rw [bitsValue_append_false, bitsValue_fixedBits_of_lt h]
    exact bitsValue_fixedBits_of_lt (lt_trans h (by
      rw [pow_succ]
      omega))

def divideZeroEncode : ZeroWordStack -> CoreStack
  | .query => .work1
  | .backup => .work3
  | .result => .work2

def divideZeroDecode : CoreStack -> Option ZeroWordStack
  | .work1 => some .query
  | .work3 => some .backup
  | .work2 => some .result
  | _ => none

def divideZeroRenaming : StackRenaming ZeroWordStack CoreStack where
  encode := divideZeroEncode
  decode := divideZeroDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;>
      simp [divideZeroDecode, divideZeroEncode] at h ⊢

inductive DividePrepareLabel
  | pushExtension
  deriving DecidableEq, Fintype, Inhabited

abbrev DivideZeroTailLabel (R : Type) :=
  Sum ZeroWordLabel (FullDivideCleanLabel R)
abbrev DivideDividendTailLabel (R : Type) :=
  Sum SymbolMoveLabel (DivideZeroTailLabel R)
abbrev DivideDivisorTailLabel (R : Type) :=
  Sum SymbolMoveLabel (DivideDividendTailLabel R)
abbrev FullDivideLabel (R : Type) :=
  Sum DividePrepareLabel (DivideDivisorTailLabel R)

def dividePrepareReset {N : Nat} (state : FullInterpreterState N) :
    FullInterpreterState N :=
  FullInterpreterState.zeroLens.put
    (FullInterpreterState.divLens.put
      (FullInterpreterState.moveLens.put state default) default) default

def dividePrepareProgram {N : Nat} {R : Type} : DividePrepareLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (FullDivideLabel R) (FullInterpreterState N)
  | .pushExtension =>
      .push .work0 (fun _ => .bit false) <|
      .load dividePrepareReset <|
      .goto fun _ => Sum.inr (Sum.inl SymbolMoveLabel.loop)

def divideZeroTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideZeroTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideZeroTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft divideZeroRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done (Sum.inl DivLabel.inspectDivisor))
    (fullDivideCleanProgram returnLabel right)

def divideDividendTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideDividendTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideDividendTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (divideZeroTailProgram returnLabel right)

def divideDivisorTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideDivisorTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideDivisorTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (divideDividendTailProgram returnLabel right)

def fullDivideProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullDivideLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullDivideLabel R)
      (FullInterpreterState N) :=
  liftRightProgram dividePrepareProgram
    (divideDivisorTailProgram returnLabel right)

def divideDivisorReadyStacks (w a d : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w a).map SparseSymbol.bit
  | .work1 => (fixedBits (w + 1) d).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def divideDividendReadyStacks (w a d : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .work7 => (fixedBits w a).reverse.map SparseSymbol.bit
  | .work1 => (fixedBits (w + 1) d).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .accumulator | .work0 | .work2 | .work3 | .work4 | .work5 | .work6 => []
  | k => base k

theorem dividePrepare_step {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    TM2.step (fullDivideProgram returnLabel right)
      (mapLabelCfg Sum.inl
        (cleanReturnCfg DividePrepareLabel.pushExtension state
          (operandResultBase w a d m base))) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        FullInterpreterState.moveLens
        (symbolMoveLocalCfg .loop
          (.bit false :: (fixedBits w d).reverse.map SparseSymbol.bit) [])
        (dividePrepareReset state) (operandResultBase w a d m base))) := by
  simp [fullDivideProgram, dividePrepareProgram, cleanReturnCfg, mapLabelCfg,
    liftRightProgram, TM2.step, lensRenamedCfg, dividePrepareReset]
  constructor
  · rfl
  · constructor
    · rfl
    · funext k
      cases k <;> simp [operandResultBase, renamedStacks,
        symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
        symbolMoveStacks]

theorem divideDivisor_bridge {N : Nat} {R : Type}
    (w a d : Nat) (hd : d < 2 ^ w) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl SymbolMoveLabel.loop : DivideDividendTailLabel R)
      (symbolMoveLocalCfg .done []
        ((.bit false :: (fixedBits w d).reverse.map SparseSymbol.bit).reverse))
      state (operandResultBase w a d m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((fixedBits w a).map SparseSymbol.bit) [])
      (FullInterpreterState.moveLens.put state default)
      (divideDivisorReadyStacks w a d m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
    operandResultBase, divideDivisorReadyStacks, renamedStacks,
    fixedBits_succ_of_lt w d hd, List.map_append, List.map_reverse]
  constructor
  · rfl
  · funext k
    cases k <;> simp [operandResultBase, divideDivisorReadyStacks,
      renamedStacks, symbolMoveCoreRenaming, symbolMoveCoreDecode,
      symbolMoveLocalCfg, symbolMoveStacks, fixedBits_succ_of_lt w d hd,
      List.map_append, List.map_reverse]

theorem divideDividend_bridge {N : Nat} {R : Type}
    (w a d : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N)
    (hzero : FullInterpreterState.zeroLens.get state = default) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl ZeroWordLabel.fill : DivideZeroTailLabel R)
      (symbolMoveLocalCfg .done []
        ((fixedBits w a).map SparseSymbol.bit).reverse)
      state (divideDivisorReadyStacks w a d m base) =
    lensRenamedCfg divideZeroRenaming FullInterpreterState.zeroLens
      (zeroWordTypedCfg .fill
        ((fixedBits (w + 1) d).map SparseSymbol.bit) [] [])
      (FullInterpreterState.moveLens.put state default)
      (divideDividendReadyStacks w a d m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
    divideDivisorReadyStacks, divideDividendReadyStacks,
    divideZeroRenaming, divideZeroDecode, zeroWordTypedCfg,
    zeroWordStacks, renamedStacks]
  constructor
  · symm
    have hz : FullInterpreterState.zeroLens.get
        (FullInterpreterState.moveLens.put state default) = default := by
      simpa using hzero
    rw [← hz, FullInterpreterState.zeroLens.put_get]
  · funext k
    cases k <;> simp [divideDivisorReadyStacks, divideDividendReadyStacks,
      divideZeroRenaming, divideZeroDecode, zeroWordTypedCfg,
      zeroWordStacks, renamedStacks, symbolMoveCoreRenaming,
      symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
      List.map_reverse]

theorem divideZero_bridge {N : Nat} {R : Type}
    (w a d : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N)
    (hdiv : FullInterpreterState.divLens.get state = default) :
    phaseReturnCfg divideZeroRenaming FullInterpreterState.zeroLens
      (Sum.inl DivLabel.inspectDivisor : FullDivideCleanLabel R)
      (zeroWordTypedCfg .done
        ((fixedBits (w + 1) d).map SparseSymbol.bit) []
        (List.replicate (w + 1) (.bit false)))
      state (divideDividendReadyStacks w a d m base) =
    lensRenamedCfg preparedDivRenaming FullInterpreterState.divLens
      (sparseDivLocalInitialCfg (fixedBits w a).reverse
        (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
      (FullInterpreterState.zeroLens.put state default)
      (preparedDivideStacks w a d m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, divideZeroRenaming,
    divideZeroDecode, zeroWordTypedCfg, zeroWordStacks,
    divideDividendReadyStacks, preparedDivideStacks,
    preparedDivRenaming, preparedDivDecode, sparseDivLocalInitialCfg,
    divStacks, mapAlphabetStacks, sparseBitEncode, renamedStacks]
  constructor
  · symm
    have hd : FullInterpreterState.divLens.get
        (FullInterpreterState.zeroLens.put state default) = default := by
      simpa using hdiv
    rw [← hd, FullInterpreterState.divLens.put_get]
  · funext k
    cases k <;> simp [divideZeroRenaming, divideZeroDecode,
      zeroWordTypedCfg, zeroWordStacks, divideDividendReadyStacks,
      preparedDivideStacks, preparedDivRenaming, preparedDivDecode,
      sparseDivLocalInitialCfg, divStacks, mapAlphabetStacks,
      sparseBitEncode, renamedStacks]

theorem dividePrepare_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d : Nat) (hd : d < 2 ^ w) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    ∃ preparedState,
      FullInterpreterState.moveLens.get preparedState = default ∧
      FullInterpreterState.literalLens.get preparedState =
        FullInterpreterState.literalLens.get state ∧
      ((fun o => o.bind (TM2.step
        (fullDivideProgram returnLabel right)))^[4 * w + 11])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a d m base)))) =
      (some <| mapLabelCfg (fun l : DivideDivisorTailLabel R => Sum.inr l) <|
        mapLabelCfg (fun l : DivideDividendTailLabel R => Sum.inr l) <|
          mapLabelCfg (fun l : DivideZeroTailLabel R => Sum.inr l) <|
            mapLabelCfg (fun l : FullDivideCleanLabel R => Sum.inr l) <|
              lensRenamedCfg (Λx := DivideCleanupTailLabel R)
                preparedDivRenaming FullInterpreterState.divLens
                (sparseDivLocalInitialCfg (fixedBits w a).reverse
                  (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
                preparedState (preparedDivideStacks w a d m base)) := by
  have hpush := dividePrepare_step returnLabel right w a d m base state
  have hpush' :
      ((fun x => x.bind (TM2.step
        (fullDivideProgram returnLabel right)))^[1])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a d m base)))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .work1 (by decide))
          FullInterpreterState.moveLens
          (symbolMoveLocalCfg .loop
            (.bit false :: (fixedBits w d).reverse.map SparseSymbol.bit) [])
          (dividePrepareReset state) (operandResultBase w a d m base))) := by
    simpa using hpush
  have hdivisor := run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .work1 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop)
    (divideDividendTailProgram returnLabel right)
    (symbolMoveLocal_correct
      (.bit false :: (fixedBits w d).reverse.map SparseSymbol.bit) []) rfl
    (dividePrepareReset state) (operandResultBase w a d m base)
  simp only [List.length_cons, List.length_map, List.length_reverse,
    fixedBits_length, List.append_nil] at hdivisor
  rw [divideDivisor_bridge (R := R) w a d hd m base
    (dividePrepareReset state)] at hdivisor
  let divisorState := FullInterpreterState.moveLens.put
    (dividePrepareReset state) default
  have hdividend := run_lensPhase_to_right
    (symbolMoveCoreRenaming .accumulator .work7 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl ZeroWordLabel.fill) (divideZeroTailProgram returnLabel right)
    (symbolMoveLocal_correct ((fixedBits w a).map SparseSymbol.bit) []) rfl
    divisorState (divideDivisorReadyStacks w a d m base)
  simp only [List.length_map, fixedBits_length, List.append_nil] at hdividend
  rw [divideDividend_bridge (R := R) w a d m base divisorState
    (by rfl)] at hdividend
  let dividendState := FullInterpreterState.moveLens.put divisorState default
  have hzero := run_lensPhase_to_right divideZeroRenaming
    FullInterpreterState.zeroLens zeroWordProgram .done (by rfl)
    (Sum.inl DivLabel.inspectDivisor) (fullDivideCleanProgram returnLabel right)
    (zeroWordTyped_correct
      ((fixedBits (w + 1) d).map SparseSymbol.bit) []) rfl
    dividendState (divideDividendReadyStacks w a d m base)
  simp only [List.length_map, fixedBits_length, List.append_nil] at hzero
  rw [divideZero_bridge (R := R) w a d m base dividendState
    (by rfl)] at hzero
  have h23 := chain_liftRightProgram (m := w + 2) (n := 2 * w + 5)
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (divideZeroTailProgram returnLabel right) hdividend hzero
  have h123 := chain_liftRightProgram
    (m := w + 3) (n := (w + 2) + (2 * w + 5))
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (divideDividendTailProgram returnLabel right) hdivisor h23
  have hrest := transport_iterate_liftRightProgram dividePrepareProgram
    (divideDivisorTailProgram returnLabel right) h123
  have hall := chain_loadInstruction_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (FullDivideLabel R) (FullInterpreterState N)) =>
      x.bind (TM2.step (fullDivideProgram returnLabel right))) hpush' hrest
  refine ⟨FullInterpreterState.zeroLens.put dividendState default, by rfl,
    by rfl, ?_⟩
  have ht : 4 * w + 11 =
      1 + ((w + 3) + ((w + 2) + (2 * w + 5))) := by omega
  rw [ht]
  simpa [fullDivideProgram, divisorState, dividendState] using hall

def embedFullDivideReturnCfg {N : Nat} {R : Type}
    (c : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) (FullDivideLabel R)
      (FullInterpreterState N) :=
  mapLabelCfg (fun l : DivideDivisorTailLabel R => Sum.inr l) <|
    mapLabelCfg (fun l : DivideDividendTailLabel R => Sum.inr l) <|
      mapLabelCfg (fun l : DivideZeroTailLabel R => Sum.inr l) <|
        mapLabelCfg (fun l : FullDivideCleanLabel R => Sum.inr l) <|
          mapLabelCfg (fun l : DivideCleanupTailLabel R => Sum.inr l) <|
            mapLabelCfg (fun l : DivideCleanupFinalLabel R => Sum.inr l) <|
              mapLabelCfg (fun l : R => Sum.inr l) c

theorem fullDivide_zero_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    ∃ finalState,
      FullInterpreterState.moveLens.get finalState = default ∧
      FullInterpreterState.literalLens.get finalState =
        FullInterpreterState.literalLens.get state ∧
      ((fun o => o.bind (TM2.step
        (fullDivideProgram returnLabel right)))^[divZeroRunTime w + 6 * w + 18])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a 0 m base)))) =
      some (embedFullDivideReturnCfg
        (cleanReturnCfg returnLabel finalState
          (operandBoundaryBase w 0 m base))) := by
  have hzeroLt : 0 < 2 ^ w := by positivity
  rcases dividePrepare_correct returnLabel right w a 0 hzeroLt m base state with
    ⟨preparedState, hmove, hprepareLiteral, hprepare⟩
  rcases fullDivideClean_zero_correct returnLabel right w a m base
      preparedState hmove with
    ⟨finalState, hfinalMove, hfinalLiteral, hclean⟩
  have hzeroLift := transport_iterate_liftRightProgram
    (lensPhaseLeft divideZeroRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done (Sum.inl DivLabel.inspectDivisor))
    (fullDivideCleanProgram returnLabel right) hclean
  have hdividendLift := transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (divideZeroTailProgram returnLabel right) hzeroLift
  have hdivisorLift := transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (divideDividendTailProgram returnLabel right) hdividendLift
  have hcleanLift := transport_iterate_liftRightProgram dividePrepareProgram
    (divideDivisorTailProgram returnLabel right) hdivisorLift
  have hall := chain_loadInstruction_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (FullDivideLabel R) (FullInterpreterState N)) =>
      x.bind (TM2.step (fullDivideProgram returnLabel right)))
    hprepare hcleanLift
  refine ⟨finalState, hfinalMove, hfinalLiteral.trans hprepareLiteral, ?_⟩
  have ht : divZeroRunTime w + 6 * w + 18 =
      (4 * w + 11) + (divZeroRunTime w + 2 * w + 7) := by omega
  rw [ht]
  simpa [fullDivideProgram, divideDivisorTailProgram,
    divideDividendTailProgram, divideZeroTailProgram,
    embedFullDivideReturnCfg] using hall

theorem fullDivide_positive_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d : Nat) (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ finalState,
      FullInterpreterState.moveLens.get finalState = default ∧
      FullInterpreterState.literalLens.get finalState =
        FullInterpreterState.literalLens.get state ∧
      ((fun o => o.bind (TM2.step
        (fullDivideProgram returnLabel right)))^[
          divPositiveRunTime w + 6 * w + 18])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a d m base)))) =
      some (embedFullDivideReturnCfg
        (cleanReturnCfg returnLabel finalState
          (operandBoundaryBase w (a / d) m base))) := by
  rcases dividePrepare_correct returnLabel right w a d hd m base state with
    ⟨preparedState, hmove, hprepareLiteral, hprepare⟩
  rcases fullDivideClean_positive_correct returnLabel right w a d ha hd0 hd
      m base preparedState hmove with
    ⟨finalState, hfinalMove, hfinalLiteral, hclean⟩
  have hzeroLift := transport_iterate_liftRightProgram
    (lensPhaseLeft divideZeroRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done (Sum.inl DivLabel.inspectDivisor))
    (fullDivideCleanProgram returnLabel right) hclean
  have hdividendLift := transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (divideZeroTailProgram returnLabel right) hzeroLift
  have hdivisorLift := transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (divideDividendTailProgram returnLabel right) hdividendLift
  have hcleanLift := transport_iterate_liftRightProgram dividePrepareProgram
    (divideDivisorTailProgram returnLabel right) hdivisorLift
  have hall := chain_loadInstruction_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (FullDivideLabel R) (FullInterpreterState N)) =>
      x.bind (TM2.step (fullDivideProgram returnLabel right)))
    hprepare hcleanLift
  refine ⟨finalState, hfinalMove, hfinalLiteral.trans hprepareLiteral, ?_⟩
  have ht : divPositiveRunTime w + 6 * w + 18 =
      (4 * w + 11) + (divPositiveRunTime w + 2 * w + 7) := by omega
  rw [ht]
  simpa [fullDivideProgram, divideDivisorTailProgram,
    divideDividendTailProgram, divideZeroTailProgram,
    embedFullDivideReturnCfg] using hall

end Lax51Proofs.RamToTM
