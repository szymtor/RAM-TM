import Lax51Proofs.RamToTM.CoreInitialization

namespace Lax51Proofs.RamToTM

open Turing TM2
open Polynomial
open Lax51.BinaryWordEncoding Lax51.RamPolytime

noncomputable section

abbrev FullInputLabel (p : Polynomial Nat) :=
  Sum (InputWidthLabel p)
    (Sum LengthPrefixLabel
      (Sum PhysicalRawLabel
        (Sum PaddingLabel (Sum FinalizeInputLabel (Sum CoreInitLabel Unit)))))

def fullInputProgram {N : Nat} (p : Polynomial Nat) : FullInputLabel p →
    TM2.Stmt WrapperAlphabet (FullInputLabel p) (WrapperState N)
  | .inl (.inr (.inr .ready)) =>
      .load (fun s => {s with core := unaryZeroWrapperLens.put s.core default}) <|
      .goto fun _ => .inr (.inl (.inl .copy))
  | .inl label => mapLabelStmt Sum.inl (inputWidthProgram p label)
  | .inr (.inl (.inr (.inr ()))) =>
      .goto fun _ => .inr (.inr (.inl .reverseSaved))
  | .inr (.inl label) =>
      mapLabelStmt (fun next => .inr (.inl next)) (lengthPrefixProgram label)
  | .inr (.inr (.inl .done)) =>
      .goto fun _ => .inr (.inr (.inr (.inl .start)))
  | .inr (.inr (.inl label)) =>
      mapLabelStmt (fun next => match next with
        | .inl phaseLabel => .inr (.inr (.inl phaseLabel))
        | .inr () => .inr (.inr (.inr (.inl .start))))
        ((physicalRawWrapperProgram (N := N)) (.inl label))
  | .inr (.inr (.inr (.inl .done))) =>
      .goto fun _ => .inr (.inr (.inr (.inr (.inl .mark))))
  | .inr (.inr (.inr (.inl label))) =>
      mapLabelStmt (fun next => match next with
        | .inl phaseLabel => .inr (.inr (.inr (.inl phaseLabel)))
        | .inr () => .inr (.inr (.inr (.inr (.inl .mark)))))
        ((paddingWrapperProgram (N := N)) (.inl label))
  | .inr (.inr (.inr (.inr (.inl .done)))) =>
      .goto fun _ => .inr (.inr (.inr (.inr (.inr (.inl .zeroCopy)))))
  | .inr (.inr (.inr (.inr (.inl label)))) =>
      mapLabelStmt (fun next => match next with
        | .inl phaseLabel => .inr (.inr (.inr (.inr (.inl phaseLabel))))
        | .inr () => .inr (.inr (.inr (.inr (.inr (.inl .zeroCopy))))))
        ((finalizeInputWrapperProgram (N := N)) (.inl label))
  | .inr (.inr (.inr (.inr (.inr (.inl .done))))) =>
      .goto fun _ => .inr (.inr (.inr (.inr (.inr (.inr ())))))
  | .inr (.inr (.inr (.inr (.inr (.inl label))))) =>
      mapLabelStmt
        (fun next => .inr (.inr (.inr (.inr (.inr (.inl next))))))
        (coreInitProgram label)
  | .inr (.inr (.inr (.inr (.inr (.inr ()))))) => .halt

def fullInputCfg {N : Nat} {p : Polynomial Nat} (label : FullInputLabel p)
    (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  ⟨some label, state, tapes⟩

def embedWidthFull {p : Polynomial Nat} : InputWidthLabel p → FullInputLabel p :=
  Sum.inl

def embedLengthFull {p : Polynomial Nat} : LengthPrefixLabel → FullInputLabel p :=
  fun label => .inr (.inl label)

theorem fullInput_lift_width {N : Nat} (p : Polynomial Nat)
    {steps : Nat}
    {c d : TM2.Cfg WrapperAlphabet (InputWidthLabel p) (WrapperState N)}
    (hrun : ((fun o => o.bind (TM2.step (inputWidthProgram p)))^[steps])
      (some c) = some d) (hd : d.l.isSome) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedWidthFull c)) =
    some (mapLabelCfg embedWidthFull d) := by
  apply iterate_mapLabelProgram_until_exit (inputWidthProgram p)
    (fullInputProgram p) embedWidthFull ?_ hrun hd
  intro label hnonhalt
  rcases label with scan | power
  · cases scan <;>
      simp [embedWidthFull, fullInputProgram, inputWidthProgram, mapLabelStmt]
        at hnonhalt ⊢
  · rcases power with power | boundary
    · simp [embedWidthFull, fullInputProgram, inputWidthProgram, mapLabelStmt,
        mapLabelStmt_comp, Function.comp_def]
    · cases boundary <;>
        simp [embedWidthFull, fullInputProgram, inputWidthProgram, mapLabelStmt,
          mapLabelStmt_comp, Function.comp_def, widthPowerCoreSpliceProgram,
          widthBoundaryCoreProgram, lensSpliceProgram, liftCoreStmt,
          lensRenameStmt] at hnonhalt ⊢

theorem fullInput_lift_length {N : Nat} (p : Polynomial Nat)
    {steps : Nat}
    {c d : TM2.Cfg WrapperAlphabet LengthPrefixLabel (WrapperState N)}
    (hrun : ((fun o => o.bind (TM2.step lengthPrefixProgram))^[steps])
      (some c) = some d) (hd : d.l.isSome) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedLengthFull c)) =
    some (mapLabelCfg embedLengthFull d) := by
  apply iterate_mapLabelProgram_until_exit lengthPrefixProgram
    (fullInputProgram p) embedLengthFull ?_ hrun hd
  intro label hnonhalt
  rcases label with zero | tail
  · cases zero <;>
      simp [embedLengthFull, fullInputProgram, lengthPrefixProgram, mapLabelStmt,
        mapLabelStmt_comp, Function.comp_def, lensRenameStmt] at hnonhalt ⊢
  · rcases tail with count | unit
    · rcases count with inc | outer
      · cases inc <;>
          simp [embedLengthFull, fullInputProgram, lengthPrefixProgram,
            mapLabelStmt, mapLabelStmt_comp, Function.comp_def,
            lensRenameStmt] at hnonhalt ⊢
      · cases outer <;>
          simp [embedLengthFull, fullInputProgram, lengthPrefixProgram,
            mapLabelStmt, mapLabelStmt_comp, Function.comp_def,
            lensRenameStmt] at hnonhalt ⊢
    · cases unit
      simp [embedLengthFull, fullInputProgram, lengthPrefixProgram] at hnonhalt

def embedRawFull {p : Polynomial Nat} :
    Sum PhysicalRawLabel Unit → FullInputLabel p
  | .inl label => .inr (.inr (.inl label))
  | .inr () => .inr (.inr (.inr (.inl .start)))

def embedPaddingFull {p : Polynomial Nat} :
    Sum PaddingLabel Unit → FullInputLabel p
  | .inl label => .inr (.inr (.inr (.inl label)))
  | .inr () => .inr (.inr (.inr (.inr (.inl .mark))))

def embedFinalizeFull {p : Polynomial Nat} :
    Sum FinalizeInputLabel Unit → FullInputLabel p
  | .inl label => .inr (.inr (.inr (.inr (.inl label))))
  | .inr () => .inr (.inr (.inr (.inr (.inr (.inl .zeroCopy)))))

def embedCoreInitFull {p : Polynomial Nat} : CoreInitLabel → FullInputLabel p :=
  fun label => .inr (.inr (.inr (.inr (.inr (.inl label)))))

theorem fullInput_lift_raw {N : Nat} (p : Polynomial Nat)
    {steps : Nat}
    {c d : TM2.Cfg WrapperAlphabet (Sum PhysicalRawLabel Unit) (WrapperState N)}
    (hrun : ((fun o => o.bind (TM2.step physicalRawWrapperProgram))^[steps])
      (some c) = some d) (hd : d.l.isSome) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedRawFull c)) =
    some (mapLabelCfg embedRawFull d) := by
  apply iterate_mapLabelProgram_until_exit physicalRawWrapperProgram
    (fullInputProgram p) embedRawFull ?_ hrun hd
  intro label hnonhalt
  rcases label with phaseLabel | unit
  · cases phaseLabel <;>
      simp [physicalRawWrapperProgram, physicalRawCoreProgram,
        liftCoreProgramSame, liftCoreStmt, collapseEmptyLabel,
        lensSpliceProgram, embedRawFull, fullInputProgram, mapLabelStmt,
        mapLabelStmt_comp, Function.comp_def, lensRenameStmt] at hnonhalt ⊢
  · cases unit
    exact (hnonhalt (by simp [physicalRawWrapperProgram, physicalRawCoreProgram,
      liftCoreProgramSame, liftCoreStmt, collapseEmptyLabel,
      lensSpliceProgram, mapLabelStmt])).elim

theorem fullInput_lift_padding {N : Nat} (p : Polynomial Nat)
    {steps : Nat}
    {c d : TM2.Cfg WrapperAlphabet (Sum PaddingLabel Unit) (WrapperState N)}
    (hrun : ((fun o => o.bind (TM2.step paddingWrapperProgram))^[steps])
      (some c) = some d) (hd : d.l.isSome) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedPaddingFull c)) =
    some (mapLabelCfg embedPaddingFull d) := by
  apply iterate_mapLabelProgram_until_exit paddingWrapperProgram
    (fullInputProgram p) embedPaddingFull ?_ hrun hd
  intro label hnonhalt
  rcases label with phaseLabel | unit
  · cases phaseLabel <;>
      simp [paddingWrapperProgram, paddingCoreProgram, liftCoreProgramSame,
        liftCoreStmt, collapseEmptyLabel, lensSpliceProgram, embedPaddingFull,
        fullInputProgram, mapLabelStmt, mapLabelStmt_comp, Function.comp_def,
        lensRenameStmt] at hnonhalt ⊢
  · cases unit
    exact (hnonhalt (by simp [paddingWrapperProgram, paddingCoreProgram,
      liftCoreProgramSame, liftCoreStmt, collapseEmptyLabel,
      lensSpliceProgram, mapLabelStmt])).elim

theorem fullInput_lift_finalize {N : Nat} (p : Polynomial Nat)
    {steps : Nat}
    {c d : TM2.Cfg WrapperAlphabet (Sum FinalizeInputLabel Unit)
      (WrapperState N)}
    (hrun : ((fun o => o.bind (TM2.step finalizeInputWrapperProgram))^[steps])
      (some c) = some d) (hd : d.l.isSome) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedFinalizeFull c)) =
    some (mapLabelCfg embedFinalizeFull d) := by
  apply iterate_mapLabelProgram_until_exit finalizeInputWrapperProgram
    (fullInputProgram p) embedFinalizeFull ?_ hrun hd
  intro label hnonhalt
  rcases label with phaseLabel | unit
  · cases phaseLabel <;>
      simp [finalizeInputWrapperProgram, finalizeInputCoreProgram,
        liftCoreProgramSame, liftCoreStmt, collapseEmptyLabel,
        lensSpliceProgram, embedFinalizeFull, fullInputProgram, mapLabelStmt,
        mapLabelStmt_comp, Function.comp_def, lensRenameStmt] at hnonhalt ⊢
  · cases unit
    exact (hnonhalt (by simp [finalizeInputWrapperProgram,
      finalizeInputCoreProgram, liftCoreProgramSame, liftCoreStmt,
      collapseEmptyLabel, lensSpliceProgram, mapLabelStmt])).elim

theorem fullInput_lift_coreInit {N : Nat} (p : Polynomial Nat)
    {steps : Nat}
    {c d : TM2.Cfg WrapperAlphabet CoreInitLabel (WrapperState N)}
    (hrun : ((fun o => o.bind (TM2.step coreInitProgram))^[steps])
      (some c) = some d) (hd : d.l.isSome) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedCoreInitFull c)) =
    some (mapLabelCfg embedCoreInitFull d) := by
  apply iterate_mapLabelProgram_until_exit coreInitProgram
    (fullInputProgram p) embedCoreInitFull ?_ hrun hd
  intro label hnonhalt
  cases label <;>
    simp [embedCoreInitFull, fullInputProgram, coreInitProgram, mapLabelStmt]
      at hnonhalt ⊢

def fullInputWidthFinal {N : Nat} (p : Polynomial Nat) (x : List Nat)
    (state : WrapperState N) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  mapLabelCfg embedWidthFull
    (inputWidthReadyCfg p (bitSize x) {state with heldInput := none}
      (inputWidthScannedStacks (encode x)))

def resetLengthPrefixState {N : Nat} (state : WrapperState N) :
    WrapperState N :=
  {state with core := unaryZeroWrapperLens.put state.core default}

def fullInputLengthStart {N : Nat} (p : Polynomial Nat) (x : List Nat)
    (state : WrapperState N) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  let c := fullInputWidthFinal p x state
  mapLabelCfg embedLengthFull
    (lengthPrefixCfg (.inl .copy) (resetLengthPrefixState c.var)
      (lengthPrefixInitialStacks (simulationWordWidth p x) x.length c.stk))

theorem fullInput_width_complete {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        4 * bitSize x + (simpleMajorantEvalCostPolynomial p).eval (bitSize x) + 5])
      (some (fullInputCfg (.inl (.inl .scan)) {state with heldInput := none}
        (inputWidthInitialStacks (encode x)))) =
    some (fullInputWidthFinal p x state) := by
  apply fullInput_lift_width p
    (inputWidth_complete_run (N := N) p x state) rfl

theorem fullInput_width_bridge {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    TM2.step (fullInputProgram p) (fullInputWidthFinal p x state) =
    some (fullInputCfg (.inr (.inl (.inl .copy)))
      (resetLengthPrefixState (fullInputWidthFinal p x state).var)
      (fullInputWidthFinal p x state).stk) := by
  rfl

theorem fullInput_width_bridge_start {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    TM2.step (fullInputProgram p) (fullInputWidthFinal p x state) =
    some (fullInputLengthStart p x state) := by
  rw [fullInput_width_bridge]
  apply congrArg some
  simp only [fullInputLengthStart, fullInputCfg, mapLabelCfg,
    lengthPrefixCfg, resetLengthPrefixState]
  congr 1
  funext k
  cases k with
  | input | output => rfl
  | core k =>
      cases k <;>
        simp [lengthPrefixInitialStacks, fullInputWidthFinal,
          inputWidthReadyCfg, inputWidthPowerFinalCfg, liftCoreCfg,
          wrapperCoreStacks, lensReturnCfg, lensRenamedCfg, renamedStacks,
          unaryPowerWrapperRenaming, unaryMulCoreRenaming, unaryMulStacks,
          unaryPowerCfg, inputWidthScannedStacks, inputSeparatorCount_encode,
          unaryMarkers, simulationWordWidth, List.replicate_succ,
          Function.update] <;> rfl

def fullInputLengthFinal {N : Nat} (p : Polynomial Nat) (x : List Nat)
    (state : WrapperState N) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  let c := fullInputWidthFinal p x state
  mapLabelCfg embedLengthFull
    (lengthPrefixCfg (.inr (.inr ()))
      (lengthPrefixFinalState c.var)
      (lengthPrefixFinalStacks (simulationWordWidth p x) x.length c.stk))

theorem fullInput_length_complete {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        2 * simulationWordWidth p x + 3 +
          (x.length * (2 * simulationWordWidth p x + 4) + 2)])
      (some (fullInputLengthStart p x state)) =
    some (fullInputLengthFinal p x state) := by
  let c := fullInputWidthFinal p x state
  have hlocal := lengthPrefix_complete
    (N := N) (w := simulationWordWidth p x) (count := x.length)
    c.var c.stk
  have hlift := fullInput_lift_length p hlocal rfl
  exact hlift

theorem fullInput_length_bridge {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    TM2.step (fullInputProgram p) (fullInputLengthFinal p x state) =
    some (fullInputCfg (.inr (.inr (.inl .reverseSaved)))
      (fullInputLengthFinal p x state).var
      (fullInputLengthFinal p x state).stk) := by
  rfl

def fullInputRawStart {N : Nat} (p : Polynomial Nat) (x : List Nat)
    (state : WrapperState N) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  let c := fullInputLengthFinal p x state
  mapLabelCfg embedRawFull
    (liftCoreCfgSame
      (lensRenamedCfg physicalRawWrapperRenaming moveWrapperLens
        (physicalRawCfg .reverseSaved
          ((encode x).reverse.map sparseOfInputSymbol) []
          ((fixedBits (simulationWordWidth p x) x.length).map
            SparseSymbol.bit) [])
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

theorem fullInput_length_bridge_start {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    TM2.step (fullInputProgram p) (fullInputLengthFinal p x state) =
    some (fullInputRawStart p x state) := by
  rw [fullInput_length_bridge]
  apply congrArg some
  simp only [fullInputRawStart, fullInputCfg, mapLabelCfg, liftCoreCfgSame,
    liftCoreCfg, lensRenamedCfg, physicalRawCfg]
  congr 1
  funext k
  cases k with
  | input | output => rfl
  | core k =>
      cases k <;>
        simp [wrapperCoreStacks, renamedStacks, physicalRawWrapperRenaming,
          physicalRawStacks, fullInputLengthFinal, lengthPrefixCfg,
          lengthPrefixFinalStacks, fullInputWidthFinal, inputWidthReadyCfg,
          inputWidthPowerFinalCfg, liftCoreCfg, lensReturnCfg,
          lensRenamedCfg, unaryMulCoreRenaming, unaryPowerCfg,
          unaryMulStacks, inputWidthScannedStacks, simulationWordWidth,
          Function.update] <;> rfl

def fullInputRawFinal {N : Nat} (p : Polynomial Nat) (x : List Nat)
    (state : WrapperState N) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  let c := fullInputLengthFinal p x state
  mapLabelCfg embedRawFull
    (liftCoreCfgSame
      (lensReturnCfg physicalRawWrapperRenaming moveWrapperLens ()
        (physicalRawCfg .done []
          (physicalPaddingRaw (simulationWordWidth p x) x) [] [])
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

theorem fullInput_raw_complete {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        bitSize x + 2 * simulationWordWidth p x + 5])
      (some (fullInputRawStart p x state)) =
    some (fullInputRawFinal p x state) := by
  let c := fullInputLengthFinal p x state
  have hlocal := physicalRaw_wrapper_correct
    (N := N) (simulationWordWidth p x) x c.var c.stk
  have hlift := fullInput_lift_raw p hlocal rfl
  exact hlift

def fullInputPaddingFinal {N : Nat} (p : Polynomial Nat) (x : List Nat)
    (state : WrapperState N) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  let c := fullInputRawFinal p x state
  let w := simulationWordWidth p x
  mapLabelCfg embedPaddingFull
    (liftCoreCfgSame
      (lensReturnCfg paddingWrapperRenaming paddingWrapperLens ()
        (paddingCfg .done default [] (unaryMarkers w) [] []
          (encodeWordList w (x.length :: x)).reverse)
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

def fullInputPaddingStart {N : Nat} (p : Polynomial Nat) (x : List Nat)
    (state : WrapperState N) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  let c := fullInputRawFinal p x state
  let w := simulationWordWidth p x
  mapLabelCfg embedPaddingFull
    (liftCoreCfgSame
      (lensRenamedCfg paddingWrapperRenaming paddingWrapperLens
        (paddingCfg .start default (physicalPaddingRaw w x)
          (unaryMarkers w) [] [] [])
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

theorem fullInputRawFinal_eq_paddingStart {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    fullInputRawFinal p x state = fullInputPaddingStart p x state := by
  simp only [fullInputPaddingStart, fullInputRawFinal, mapLabelCfg,
    liftCoreCfgSame, liftCoreCfg, lensReturnCfg, lensRenamedCfg,
    physicalRawCfg, paddingCfg]
  congr 1
  funext k
  cases k with
  | input | output => rfl
  | core k => cases k <;>
      simp [wrapperCoreStacks, renamedStacks, physicalRawWrapperRenaming,
        paddingWrapperRenaming, physicalRawStacks, paddingStacks,
        Function.update] <;> rfl

theorem fullInput_padding_complete {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N)
    (hlen : x.length < 2 ^ simulationWordWidth p x)
    (hfit : ∀ n ∈ x, n < 2 ^ simulationWordWidth p x) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        1 + (x.length + 1) * (3 * simulationWordWidth p x + 5) + 1])
      (some (fullInputPaddingStart p x state)) =
    some (fullInputPaddingFinal p x state) := by
  let c := fullInputRawFinal p x state
  let w := simulationWordWidth p x
  have hlocal := padding_wrapper_correct
    (N := N) w x hlen hfit c.var c.stk
  have hlift := fullInput_lift_padding p hlocal rfl
  exact hlift

def fullInputFinalizeFinal {N : Nat} (p : Polynomial Nat) (x : List Nat)
    (state : WrapperState N) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  let c := fullInputPaddingFinal p x state
  let w := simulationWordWidth p x
  mapLabelCfg embedFinalizeFull
    (liftCoreCfgSame
      (lensReturnCfg finalizeInputWrapperRenaming moveWrapperLens ()
        (finalizeInputCfg .done [] (encodeInputStack w (x.length :: x)))
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

def fullInputFinalizeStart {N : Nat} (p : Polynomial Nat) (x : List Nat)
    (state : WrapperState N) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  let c := fullInputPaddingFinal p x state
  let w := simulationWordWidth p x
  mapLabelCfg embedFinalizeFull
    (liftCoreCfgSame
      (lensRenamedCfg finalizeInputWrapperRenaming moveWrapperLens
        (finalizeInputCfg .mark (encodeWordList w (x.length :: x)).reverse [])
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

theorem fullInputPaddingFinal_eq_finalizeStart {N : Nat}
    (p : Polynomial Nat) (x : List Nat) (state : WrapperState N) :
    fullInputPaddingFinal p x state = fullInputFinalizeStart p x state := by
  simp only [fullInputFinalizeStart, fullInputPaddingFinal, mapLabelCfg,
    liftCoreCfgSame, liftCoreCfg, lensReturnCfg, lensRenamedCfg,
    paddingCfg, finalizeInputCfg]
  congr 1
  funext k
  cases k with
  | input | output => rfl
  | core k => cases k <;>
      simp [wrapperCoreStacks, renamedStacks, paddingWrapperRenaming,
        finalizeInputWrapperRenaming, paddingStacks, finalizeInputStacks,
        encodeInputStack, Function.update] <;> rfl

theorem fullInput_finalize_complete {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        (encodeWordList (simulationWordWidth p x) (x.length :: x)).length + 4])
      (some (fullInputFinalizeStart p x state)) =
    some (fullInputFinalizeFinal p x state) := by
  let c := fullInputPaddingFinal p x state
  let w := simulationWordWidth p x
  have hlocal := finalizeInput_wrapper_correct
    (N := N) w (x.length :: x) c.var c.stk
  have hlift := fullInput_lift_finalize p hlocal rfl
  exact hlift

def fullInputCoreFinal {N : Nat} (p : Polynomial Nat) (x : List Nat)
    (state : WrapperState N) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  let c := fullInputFinalizeFinal p x state
  mapLabelCfg embedCoreInitFull
    (coreInitCfg .done default
      (coreInitFinalStacks (simulationWordWidth p x) c.stk))

def fullInputCoreStart {N : Nat} (p : Polynomial Nat) (x : List Nat)
    (state : WrapperState N) :
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N) :=
  let c := fullInputFinalizeFinal p x state
  mapLabelCfg embedCoreInitFull
    (coreInitCfg .zeroCopy c.var
      (Function.update
        (Function.update c.stk (.core .work1)
          (unaryMarkers (bitSize x + 1)))
        (.core .work3) (unaryMarkers (simulationWordWidth p x))))

theorem fullInputFinalizeFinal_eq_coreStart {N : Nat}
    (p : Polynomial Nat) (x : List Nat) (state : WrapperState N) :
    fullInputFinalizeFinal p x state = fullInputCoreStart p x state := by
  simp only [fullInputCoreStart, fullInputFinalizeFinal, mapLabelCfg,
    liftCoreCfgSame, liftCoreCfg, lensReturnCfg, finalizeInputCfg, coreInitCfg]
  congr 1
  funext k
  cases k with
  | input | output => rfl
  | core k => cases k <;>
      simp [wrapperCoreStacks, renamedStacks, finalizeInputWrapperRenaming,
        finalizeInputStacks, fullInputPaddingFinal, fullInputRawFinal,
        fullInputLengthFinal, fullInputWidthFinal, lensReturnCfg,
        lensRenamedCfg, liftCoreCfgSame, liftCoreCfg,
        paddingWrapperRenaming, physicalRawWrapperRenaming,
        paddingCfg, paddingStacks, physicalRawCfg, physicalRawStacks,
        lengthPrefixCfg, lengthPrefixFinalStacks, inputWidthReadyCfg,
        inputWidthPowerFinalCfg, unaryMulCoreRenaming, unaryPowerCfg,
        unaryMulStacks, inputWidthScannedStacks, unaryMarkers,
        bitSize, Function.update] <;> rfl

theorem fullInput_core_complete {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        3 * simulationWordWidth p x + (bitSize x + 1) + 5])
      (some (fullInputCoreStart p x state)) =
    some (fullInputCoreFinal p x state) := by
  let c := fullInputFinalizeFinal p x state
  let w := simulationWordWidth p x
  have hlocal := coreInit_correct (N := N) (w := w) c.var
    (unaryMarkers (bitSize x + 1)) c.stk
    (by simp [c, fullInputFinalizeFinal, fullInputPaddingFinal,
      fullInputRawFinal, fullInputLengthFinal, fullInputWidthFinal,
      mapLabelCfg, liftCoreCfgSame, liftCoreCfg, wrapperCoreStacks,
      collapseEmptyLabel, lensReturnCfg, lensRenamedCfg, renamedStacks,
      finalizeInputWrapperRenaming, paddingWrapperRenaming,
      physicalRawWrapperRenaming, unaryPowerWrapperRenaming,
      unaryMulCoreRenaming, finalizeInputCfg, finalizeInputStacks,
      paddingCfg, paddingStacks, physicalRawCfg, physicalRawStacks,
      inputWidthReadyCfg, inputWidthPowerFinalCfg, unaryMulStacks,
      lengthPrefixCfg, lengthPrefixFinalStacks, inputWidthScannedStacks,
      Function.update] <;> rfl)
    (by simp [c, fullInputFinalizeFinal, fullInputPaddingFinal,
      mapLabelCfg, liftCoreCfgSame, liftCoreCfg, wrapperCoreStacks,
      collapseEmptyLabel, lensReturnCfg, lensRenamedCfg, renamedStacks,
      finalizeInputWrapperRenaming, paddingWrapperRenaming,
      finalizeInputCfg, finalizeInputStacks, paddingCfg, paddingStacks,
      lengthPrefixCfg, lengthPrefixFinalStacks, Function.update] <;> rfl)
    (by simp [c, fullInputFinalizeFinal, fullInputPaddingFinal,
      fullInputRawFinal, fullInputLengthFinal, fullInputWidthFinal,
      mapLabelCfg, liftCoreCfgSame, liftCoreCfg, wrapperCoreStacks,
      collapseEmptyLabel, lensReturnCfg, lensRenamedCfg, renamedStacks,
      finalizeInputWrapperRenaming, paddingWrapperRenaming,
      physicalRawWrapperRenaming, unaryPowerWrapperRenaming,
      finalizeInputCfg, finalizeInputStacks, paddingCfg, paddingStacks,
      physicalRawCfg, physicalRawStacks, inputWidthReadyCfg,
      inputWidthPowerFinalCfg, lengthPrefixCfg, lengthPrefixFinalStacks,
      inputWidthScannedStacks, Function.update] <;> rfl)
    (by simp [c, fullInputFinalizeFinal, fullInputPaddingFinal,
      fullInputRawFinal, fullInputLengthFinal, fullInputWidthFinal,
      mapLabelCfg, liftCoreCfgSame, liftCoreCfg, wrapperCoreStacks,
      collapseEmptyLabel, lensReturnCfg, lensRenamedCfg, renamedStacks,
      finalizeInputWrapperRenaming, paddingWrapperRenaming,
      physicalRawWrapperRenaming, unaryPowerWrapperRenaming,
      finalizeInputCfg, finalizeInputStacks, paddingCfg, paddingStacks,
      physicalRawCfg, physicalRawStacks, inputWidthReadyCfg,
      inputWidthPowerFinalCfg, lengthPrefixCfg, lengthPrefixFinalStacks,
      inputWidthScannedStacks, Function.update] <;> rfl)
  have hlift := fullInput_lift_coreInit p hlocal rfl
  simpa [c, w, fullInputCoreStart, fullInputCoreFinal, unaryMarkers] using hlift

def fullInputCost (p : Polynomial Nat) (x : List Nat) : Nat :=
  (4 * bitSize x +
      (simpleMajorantEvalCostPolynomial p).eval (bitSize x) + 5) + 1 +
  (2 * simulationWordWidth p x + 3 +
      (x.length * (2 * simulationWordWidth p x + 4) + 2)) + 1 +
  (bitSize x + 2 * simulationWordWidth p x + 5) +
  (1 + (x.length + 1) * (3 * simulationWordWidth p x + 5) + 1) +
  ((encodeWordList (simulationWordWidth p x) (x.length :: x)).length + 4) +
  (3 * simulationWordWidth p x + (bitSize x + 1) + 5)

theorem fullInput_complete {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N)
    (hlen : x.length < 2 ^ simulationWordWidth p x)
    (hfit : ∀ n ∈ x, n < 2 ^ simulationWordWidth p x) :
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[fullInputCost p x])
      (some (fullInputCfg (.inl (.inl .scan)) {state with heldInput := none}
        (inputWidthInitialStacks (encode x)))) =
    some (fullInputCoreFinal p x state) := by
  have h₁ := fullInput_width_complete (N := N) p x state
  have h₂step := fullInput_width_bridge_start (N := N) p x state
  have h₂ :
      ((fun o => o.bind (TM2.step (fullInputProgram p)))^[1])
        (some (fullInputWidthFinal p x state)) =
      some (fullInputLengthStart p x state) := by simpa using h₂step
  have h₃ := fullInput_length_complete (N := N) p x state
  have h₄step := fullInput_length_bridge_start (N := N) p x state
  have h₄ :
      ((fun o => o.bind (TM2.step (fullInputProgram p)))^[1])
        (some (fullInputLengthFinal p x state)) =
      some (fullInputRawStart p x state) := by simpa using h₄step
  have h₅ := fullInput_raw_complete (N := N) p x state
  have h₆ := fullInput_padding_complete (N := N) p x state hlen hfit
  have h₇ := fullInput_finalize_complete (N := N) p x state
  have h₈ := fullInput_core_complete (N := N) p x state
  have h₆' := (congrArg
    (fun cfg => ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
      1 + (x.length + 1) * (3 * simulationWordWidth p x + 5) + 1]) cfg)
    (congrArg some (fullInputRawFinal_eq_paddingStart (N := N) p x state))).trans h₆
  have h₇' := (congrArg
    (fun cfg => ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
      (encodeWordList (simulationWordWidth p x) (x.length :: x)).length + 4]) cfg)
    (congrArg some
      (fullInputPaddingFinal_eq_finalizeStart (N := N) p x state))).trans h₇
  have h₈' := (congrArg
    (fun cfg => ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
      3 * simulationWordWidth p x + (bitSize x + 1) + 5]) cfg)
    (congrArg some
      (fullInputFinalizeFinal_eq_coreStart (N := N) p x state))).trans h₈
  have h := chain_iterations _ (chain_iterations _ (chain_iterations _
    (chain_iterations _ (chain_iterations _ (chain_iterations _
      (chain_iterations _ h₁ h₂) h₃) h₄) h₅) h₆') h₇') h₈'
  simpa [fullInputCost, Nat.add_assoc] using h

theorem fullInputCoreFinal_eq_canonical {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    fullInputCoreFinal p x state =
      fullInputCfg
        (.inr (.inr (.inr (.inr (.inr (.inl .done)))))) default
        (wrapperCoreStacks
          (coreStacks (simulationWordWidth p x) (sparseInitState (x.length :: x)))
          [] []) := by
  simp only [fullInputCoreFinal, mapLabelCfg, coreInitCfg, fullInputCfg]
  congr 1
  funext k
  cases k with
    | input =>
        simp [fullInputCoreFinal, coreInitFinalStacks, fullInputFinalizeFinal,
          fullInputPaddingFinal, fullInputRawFinal, fullInputLengthFinal,
          fullInputWidthFinal, wrapperCoreStacks, inputWidthInitialStacks,
          inputWidthScannedStacks, mapLabelCfg, liftCoreCfgSame, liftCoreCfg,
          collapseEmptyLabel, lensReturnCfg,
          lensRenamedCfg, renamedStacks, finalizeInputWrapperRenaming,
          paddingWrapperRenaming, physicalRawWrapperRenaming,
          unaryPowerWrapperRenaming, unaryMulCoreRenaming, coreStacks,
          sparseInitState, Function.update] <;> rfl
    | output =>
        simp [fullInputCoreFinal, coreInitFinalStacks, fullInputFinalizeFinal,
          fullInputPaddingFinal, fullInputRawFinal, fullInputLengthFinal,
          fullInputWidthFinal, wrapperCoreStacks, inputWidthInitialStacks,
          inputWidthScannedStacks, mapLabelCfg, liftCoreCfgSame, liftCoreCfg,
          collapseEmptyLabel, lensReturnCfg,
          lensRenamedCfg, renamedStacks, finalizeInputWrapperRenaming,
          paddingWrapperRenaming, physicalRawWrapperRenaming,
          unaryPowerWrapperRenaming, unaryMulCoreRenaming,
          Function.update] <;> rfl
    | core k =>
        cases k <;>
          simp [fullInputCoreFinal, coreInitFinalStacks,
            fullInputFinalizeFinal, fullInputPaddingFinal, fullInputRawFinal,
            fullInputLengthFinal, fullInputWidthFinal, wrapperCoreStacks,
            inputWidthInitialStacks, inputWidthScannedStacks, mapLabelCfg,
            liftCoreCfgSame, liftCoreCfg, collapseEmptyLabel,
            lensReturnCfg, lensRenamedCfg, renamedStacks,
            finalizeInputWrapperRenaming, paddingWrapperRenaming,
            physicalRawWrapperRenaming, unaryPowerWrapperRenaming,
            unaryMulCoreRenaming, unaryMulStacks, finalizeInputCfg,
            finalizeInputStacks, paddingCfg, paddingStacks, physicalRawCfg,
            physicalRawStacks, lengthPrefixCfg, lengthPrefixFinalStacks,
            inputWidthReadyCfg, inputWidthPowerFinalCfg, coreStacks,
            sparseInitState, encodeAccumulator, encodeMemoryStack,
            encodeOutputStack, encodeInputStack, Function.update] <;> rfl

noncomputable def simulationWidthPolynomial (p : Polynomial Nat) :
    Polynomial Nat := polynomialSimpleMajorant p + 1

@[simp] theorem simulationWidthPolynomial_eval (p : Polynomial Nat) (n : Nat) :
    (simulationWidthPolynomial p).eval n =
      (polynomialSimpleMajorant p).eval n + 1 := by
  simp [simulationWidthPolynomial]

noncomputable def fullInputCostPolynomial (p : Polynomial Nat) :
    Polynomial Nat :=
  let w := simulationWidthPolynomial p
  (4 * X + simpleMajorantEvalCostPolynomial p + 5) + 1 +
  (2 * w + 3 + (X * (2 * w + 4) + 2)) + 1 +
  (X + 2 * w + 5) +
  (1 + (X + 1) * (3 * w + 5) + 1) +
  ((X + 1) * (w + 1) + 4) +
  (3 * w + (X + 1) + 5)

@[simp] theorem fullInputCostPolynomial_eval (p : Polynomial Nat) (n : Nat) :
    (fullInputCostPolynomial p).eval n =
      let w := (polynomialSimpleMajorant p).eval n + 1
      (4 * n + (simpleMajorantEvalCostPolynomial p).eval n + 5) + 1 +
      (2 * w + 3 + (n * (2 * w + 4) + 2)) + 1 +
      (n + 2 * w + 5) +
      (1 + (n + 1) * (3 * w + 5) + 1) +
      ((n + 1) * (w + 1) + 4) +
      (3 * w + (n + 1) + 5) := by
  simp [fullInputCostPolynomial, simulationWidthPolynomial]

theorem fullInputCost_le_polynomial (p : Polynomial Nat) (x : List Nat) :
    fullInputCost p x ≤ (fullInputCostPolynomial p).eval (bitSize x) := by
  rw [fullInputCostPolynomial_eval]
  have hx := Lax51Proofs.Encoding.length_le_bitSize x
  simp only [fullInputCost, simulationWordWidth]
  simp only [encodeWordList_length, List.length_cons]
  gcongr


end

end Lax51Proofs.RamToTM
