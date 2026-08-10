import Lax51Proofs.RamToTM.UnaryZeroWordMacro

namespace Lax51Proofs.RamToTM

open Turing TM2

noncomputable section

def unaryZeroWrapperRenaming : StackRenaming UnaryZeroStack CoreStack where
  encode
    | .width => .work3
    | .word => .work6
    | .backup => .work7
  decode
    | .work3 => some .width
    | .work6 => some .word
    | .work7 => some .backup
    | _ => none
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k <;> cases k' <;> simp_all

def unaryZeroWrapperLens {N : Nat} :
    StateLens SymbolMoveControl (FullInterpreterState N) :=
  FullInterpreterState.moveLens

def countIncrementWrapperRenaming :
    StackRenaming CountIncrementStack CoreStack where
  encode
    | .count => .work2
    | .word => .work6
    | .temp => .work7
  decode
    | .work2 => some .count
    | .work6 => some .word
    | .work7 => some .temp
    | _ => none
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k <;> cases k' <;> simp_all

def incrementWrapperLens {N : Nat} :
    StateLens IncrementControl (FullInterpreterState N) where
  get s := ⟨s.lookupFound, (FullInterpreterState.moveLens.get s).held⟩
  put s c := FullInterpreterState.moveLens.put
    {s with lookupFound := c.carry} ⟨c.held⟩
  get_put := by intros; rfl
  put_get := by intro s; cases s <;> rfl
  put_put := by intros; rfl

abbrev LengthPrefixLabel :=
  Sum UnaryZeroLabel (Sum CountIncrementLabel Unit)

def zeroCoreSplice {N : Nat} :
    Sum UnaryZeroLabel Unit →
      TM2.Stmt (fun _ : CoreStack => SparseSymbol)
        (Sum UnaryZeroLabel Unit) (FullInterpreterState N) :=
  lensSpliceProgram unaryZeroWrapperRenaming unaryZeroWrapperLens
    unaryZeroProgram .done () (fun _ => .halt)

def countCoreSplice {N : Nat} :
    Sum CountIncrementLabel Unit →
      TM2.Stmt (fun _ : CoreStack => SparseSymbol)
        (Sum CountIncrementLabel Unit) (FullInterpreterState N) :=
  lensSpliceProgram countIncrementWrapperRenaming incrementWrapperLens
    countIncrementProgram (.inr .done) () (fun _ => .halt)

def embedLiftedZeroLengthLabel : Sum (Sum UnaryZeroLabel Unit) Empty →
    LengthPrefixLabel
  | .inl (.inl label) => .inl label
  | .inl (.inr ()) => .inr (.inl (.inr .loop))
  | .inr impossible => nomatch impossible

def embedLiftedCountLengthLabel : Sum (Sum CountIncrementLabel Unit) Empty →
    LengthPrefixLabel
  | .inl (.inl label) => .inr (.inl label)
  | .inl (.inr ()) => .inr (.inr ())
  | .inr impossible => nomatch impossible

def lengthPrefixProgram {N : Nat} : LengthPrefixLabel →
    TM2.Stmt WrapperAlphabet LengthPrefixLabel (WrapperState N)
  | .inl .done => .goto fun _ => .inr (.inl (.inr .loop))
  | .inl label =>
      mapLabelStmt embedLiftedZeroLengthLabel <|
        liftCoreStmt (N := N) (X := Empty)
          (zeroCoreSplice (.inl label))
  | .inr (.inl (.inr .done)) => .goto fun _ => .inr (.inr ())
  | .inr (.inl label) =>
      mapLabelStmt embedLiftedCountLengthLabel <|
        liftCoreStmt (N := N) (X := Empty)
          (countCoreSplice (.inl label))
  | .inr (.inr ()) => .halt

def lengthPrefixCfg {N : Nat} (label : LengthPrefixLabel)
    (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.Cfg WrapperAlphabet LengthPrefixLabel (WrapperState N) :=
  ⟨some label, state, tapes⟩

def zeroWrapperSplice {N : Nat} :
    Sum (Sum UnaryZeroLabel Unit) Empty →
      TM2.Stmt WrapperAlphabet (Sum (Sum UnaryZeroLabel Unit) Empty)
        (WrapperState N) :=
  liftCoreProgram (zeroCoreSplice (N := N))
    (fun impossible : Empty => nomatch impossible)

def embedZeroLengthLabel : Sum UnaryZeroLabel Unit → LengthPrefixLabel
  | .inl label => .inl label
  | .inr () => .inr (.inl (.inr .loop))

theorem lengthPrefix_zero_run {N w : Nat} (state : WrapperState N)
    (ambient : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step lengthPrefixProgram))^[2 * w + 3])
      (some (mapLabelCfg embedLiftedZeroLengthLabel
        (liftCoreCfg (X := Empty)
          (lensRenamedCfg unaryZeroWrapperRenaming unaryZeroWrapperLens
            (unaryZeroCfg .copy (unaryMarkers w) [] []) state.core
            (fun k => ambient (.core k))) state
          (ambient .input) (ambient .output)))) =
    some (mapLabelCfg embedLiftedZeroLengthLabel
      (liftCoreCfg (X := Empty)
        (lensReturnCfg unaryZeroWrapperRenaming unaryZeroWrapperLens ()
        (unaryZeroCfg .done (unaryMarkers w)
          ((fixedBits w 0).map SparseSymbol.bit) []) state.core
          (fun k => ambient (.core k))) state
        (ambient .input) (ambient .output))) := by
  have hcore := transport_lensHaltingMacro_and_return
    unaryZeroWrapperRenaming unaryZeroWrapperLens unaryZeroProgram .done (by rfl)
    () (fun _ => .halt) (unaryZero_correct w) rfl state.core
    (fun k => ambient (.core k))
  rw [show 2 * w + 2 + 1 = 2 * w + 3 by omega] at hcore
  have hlift := iterate_liftCoreProgram (zeroCoreSplice (N := N))
    (fun impossible : Empty => nomatch impossible) _ _ state
    (ambient .input) (ambient .output) hcore
  apply iterate_mapLabelProgram_until_exit (zeroWrapperSplice (N := N))
    lengthPrefixProgram embedLiftedZeroLengthLabel ?_ hlift (by rfl)
  · intro label hnonhalt
    cases label with
    | inl label =>
        cases label with
        | inl label => cases label <;>
            simp [lengthPrefixProgram, zeroWrapperSplice,
              zeroCoreSplice, liftCoreProgram, lensSpliceProgram,
              liftCoreStmt, mapLabelStmt, lensRenameStmt,
              embedLiftedZeroLengthLabel] at hnonhalt ⊢
        | inr unit => cases unit
                      exact (hnonhalt rfl).elim
    | inr impossible => nomatch impossible

def countWrapperSplice {N : Nat} :
    Sum (Sum CountIncrementLabel Unit) Empty →
      TM2.Stmt WrapperAlphabet (Sum (Sum CountIncrementLabel Unit) Empty)
        (WrapperState N) :=
  liftCoreProgram (countCoreSplice (N := N))
    (fun impossible : Empty => nomatch impossible)

def embedCountLengthLabel : Sum CountIncrementLabel Unit → LengthPrefixLabel
  | .inl label => .inr (.inl label)
  | .inr () => .inr (.inr ())

theorem lengthPrefix_count_run {N count w : Nat} (state : WrapperState N)
    (ambient : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step lengthPrefixProgram))^[
        count * (2 * w + 4) + 2])
      (some (mapLabelCfg embedLiftedCountLengthLabel
        (liftCoreCfg (X := Empty)
          (lensRenamedCfg countIncrementWrapperRenaming incrementWrapperLens
          (countIncrementCfg (.inr .loop) (unaryMarkers count)
            ((fixedBits w 0).map SparseSymbol.bit) []) state.core
            (fun k => ambient (.core k))) state
          (ambient .input) (ambient .output)))) =
    some (mapLabelCfg embedLiftedCountLengthLabel
      (liftCoreCfg (X := Empty)
        (lensReturnCfg countIncrementWrapperRenaming incrementWrapperLens ()
        (countIncrementCfg (.inr .done) []
          ((fixedBits w count).map SparseSymbol.bit) []) state.core
          (fun k => ambient (.core k))) state
        (ambient .input) (ambient .output))) := by
  have hcore := transport_lensHaltingMacro_and_return
    countIncrementWrapperRenaming incrementWrapperLens countIncrementProgram
    (.inr .done) (by rfl) () (fun _ => .halt)
    (countIncrement_correct count w) rfl state.core
    (fun k => ambient (.core k))
  rw [show count * (2 * w + 4) + 1 + 1 =
    count * (2 * w + 4) + 2 by omega] at hcore
  have hlift := iterate_liftCoreProgram (countCoreSplice (N := N))
    (fun impossible : Empty => nomatch impossible) _ _ state
    (ambient .input) (ambient .output) hcore
  apply iterate_mapLabelProgram_until_exit (countWrapperSplice (N := N))
    lengthPrefixProgram embedLiftedCountLengthLabel ?_ hlift (by rfl)
  · intro label hnonhalt
    cases label with
    | inl label =>
        cases label with
        | inl label =>
            rcases label with label | label <;> cases label <;>
              simp [lengthPrefixProgram, countWrapperSplice,
                countCoreSplice, liftCoreProgram, lensSpliceProgram,
                liftCoreStmt, mapLabelStmt, lensRenameStmt,
                embedLiftedCountLengthLabel] at hnonhalt ⊢
        | inr unit => cases unit
                      exact (hnonhalt rfl).elim
    | inr impossible => nomatch impossible

theorem lengthPrefix_count_run_from {N count w : Nat} (state : WrapperState N)
    (ambient : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step lengthPrefixProgram))^[
        count * (2 * w + 4) + 2])
      (some (mapLabelCfg embedLiftedCountLengthLabel
        (liftCoreCfg (X := Empty)
          (lensRenamedCfg countIncrementWrapperRenaming incrementWrapperLens
          (countIncrementCfgState (.inr .loop)
            (incrementWrapperLens.get state.core) (unaryMarkers count)
            ((fixedBits w 0).map SparseSymbol.bit) []) state.core
            (fun k => ambient (.core k))) state
          (ambient .input) (ambient .output)))) =
    some (mapLabelCfg embedLiftedCountLengthLabel
      (liftCoreCfg (X := Empty)
        (lensReturnCfg countIncrementWrapperRenaming incrementWrapperLens ()
        (countIncrementCfg (.inr .done) []
          ((fixedBits w count).map SparseSymbol.bit) []) state.core
          (fun k => ambient (.core k))) state
        (ambient .input) (ambient .output))) := by
  have hcore := transport_lensHaltingMacro_and_return
    countIncrementWrapperRenaming incrementWrapperLens countIncrementProgram
    (.inr .done) (by rfl) () (fun _ => .halt)
    (countIncrement_correct_from (incrementWrapperLens.get state.core) count w)
    rfl state.core (fun k => ambient (.core k))
  rw [show count * (2 * w + 4) + 1 + 1 =
    count * (2 * w + 4) + 2 by omega] at hcore
  have hlift := iterate_liftCoreProgram (countCoreSplice (N := N))
    (fun impossible : Empty => nomatch impossible) _ _ state
    (ambient .input) (ambient .output) hcore
  apply iterate_mapLabelProgram_until_exit (countWrapperSplice (N := N))
    lengthPrefixProgram embedLiftedCountLengthLabel ?_ hlift (by rfl)
  · intro label hnonhalt
    cases label with
    | inl label =>
        cases label with
        | inl label =>
            rcases label with label | label <;> cases label <;>
              simp [lengthPrefixProgram, countWrapperSplice,
                countCoreSplice, liftCoreProgram, lensSpliceProgram,
                liftCoreStmt, mapLabelStmt, lensRenameStmt,
                embedLiftedCountLengthLabel] at hnonhalt ⊢
        | inr unit => cases unit
                      exact (hnonhalt rfl).elim
    | inr impossible => nomatch impossible

def lengthPrefixInitialStacks (w count : Nat)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    (k : WrapperStack) → List (WrapperAlphabet k) :=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (.core .work2) (unaryMarkers count))
          (.core .work3) (unaryMarkers w))
        (.core .work6) [])
      (.core .work7) []

def lengthPrefixFinalStacks (w count : Nat)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    (k : WrapperStack) → List (WrapperAlphabet k) :=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (.core .work2) [])
          (.core .work3) (unaryMarkers w))
        (.core .work6) ((fixedBits w count).map SparseSymbol.bit))
      (.core .work7) []

def lengthPrefixFinalState {N : Nat} (state : WrapperState N) :
    WrapperState N :=
  let afterZero := unaryZeroWrapperLens.put state.core default
  {state with core := incrementWrapperLens.put afterZero default}

theorem lengthPrefix_complete {N w count : Nat} (state : WrapperState N)
    (base : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step lengthPrefixProgram))^[
        2 * w + 3 + (count * (2 * w + 4) + 2)])
      (some (lengthPrefixCfg (.inl .copy)
        {state with core := unaryZeroWrapperLens.put state.core default}
        (lengthPrefixInitialStacks w count base))) =
    some (lengthPrefixCfg (.inr (.inr ()))
      (lengthPrefixFinalState state)
      (lengthPrefixFinalStacks w count base)) := by
  let state₁ : WrapperState N :=
    {state with core := unaryZeroWrapperLens.put state.core default}
  have hzero := lengthPrefix_zero_run (N := N) (w := w) state
    (lengthPrefixInitialStacks w count base)
  have hcount := lengthPrefix_count_run_from (N := N) (count := count) (w := w)
    state₁ (lengthPrefixInitialStacks w count base)
  have hmid :
      mapLabelCfg embedLiftedZeroLengthLabel
        (liftCoreCfg (X := Empty)
          (lensReturnCfg unaryZeroWrapperRenaming unaryZeroWrapperLens ()
            (unaryZeroCfg .done (unaryMarkers w)
              ((fixedBits w 0).map SparseSymbol.bit) []) state.core
            (fun k => lengthPrefixInitialStacks w count base (.core k)))
          state (lengthPrefixInitialStacks w count base .input)
          (lengthPrefixInitialStacks w count base .output)) =
      mapLabelCfg embedLiftedCountLengthLabel
        (liftCoreCfg (X := Empty)
          (lensRenamedCfg countIncrementWrapperRenaming incrementWrapperLens
            (countIncrementCfgState (.inr .loop)
              (incrementWrapperLens.get state₁.core) (unaryMarkers count)
              ((fixedBits w 0).map SparseSymbol.bit) []) state₁.core
            (fun k => lengthPrefixInitialStacks w count base (.core k)))
          state₁ (lengthPrefixInitialStacks w count base .input)
          (lengthPrefixInitialStacks w count base .output)) := by
    simp [state₁, mapLabelCfg, liftCoreCfg, lensReturnCfg, lensRenamedCfg,
      unaryZeroCfg, unaryZeroStacks, countIncrementCfgState,
      countIncrementStacks, renamedStacks, unaryZeroWrapperRenaming,
      countIncrementWrapperRenaming, lengthPrefixInitialStacks,
      wrapperCoreStacks,
      fixedBits_zero, Function.update]
    constructor
    · rfl
    constructor
    · rw [(incrementWrapperLens (N := N)).put_get]
      rfl
    · funext k
      cases k with
      | input | output => rfl
      | core k =>
          cases k <;> simp [wrapperCoreStacks, renamedStacks,
            unaryZeroWrapperRenaming, countIncrementWrapperRenaming,
            unaryZeroStacks, countIncrementStacks,
            lengthPrefixInitialStacks, Function.update]
  rw [← hmid] at hcount
  have h := chain_iterations _ hzero hcount
  convert h using 1
  case h.e'_2 =>
    congr 2
    simp [lengthPrefixCfg, mapLabelCfg, liftCoreCfg, lensRenamedCfg,
      unaryZeroCfg, unaryZeroStacks, renamedStacks,
      unaryZeroWrapperRenaming, lengthPrefixInitialStacks,
      wrapperCoreStacks, Function.update]
    constructor
    · rfl
    constructor
    · rfl
    · funext k
      cases k with
      | input | output => rfl
      | core k => cases k <;> simp [renamedStacks, unaryZeroStacks,
          lengthPrefixInitialStacks, wrapperCoreStacks, Function.update] <;> rfl
  case h.e'_3 =>
    congr 2
    simp [lengthPrefixCfg, lengthPrefixFinalState, lengthPrefixFinalStacks,
      mapLabelCfg, liftCoreCfg, lensReturnCfg, countIncrementCfg,
      countIncrementStacks, renamedStacks, countIncrementWrapperRenaming,
      state₁, wrapperCoreStacks, lengthPrefixInitialStacks,
      Function.update]
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;> simp [renamedStacks, countIncrementStacks,
        countIncrementWrapperRenaming, lengthPrefixInitialStacks,
        lengthPrefixFinalStacks, wrapperCoreStacks, Function.update] <;> rfl

end

end Lax51Proofs.RamToTM
