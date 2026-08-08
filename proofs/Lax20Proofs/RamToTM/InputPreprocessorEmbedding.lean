import Lax20Proofs.RamToTM.FinalizeInputMacro

namespace Lax20Proofs.RamToTM

open Turing TM2
open Lax20.BinaryWordEncoding Lax20.RamPolytime

noncomputable section

def physicalRawWrapperRenaming : StackRenaming PhysicalRawStack CoreStack where
  encode
    | .saved => .work0
    | .raw => .work4
    | .length => .work6
    | .temp => .work2
  decode
    | .work0 => some .saved
    | .work4 => some .raw
    | .work6 => some .length
    | .work2 => some .temp
    | _ => none
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k <;> cases k' <;> simp_all

def moveWrapperLens {N : Nat} :
    StateLens SymbolMoveControl (FullInterpreterState N) :=
  FullInterpreterState.moveLens

def paddingWrapperRenaming : StackRenaming PaddingStack CoreStack where
  encode
    | .raw => .work4
    | .width => .work3
    | .counter => .work2
    | .backup => .work7
    | .output => .work5
  decode
    | .work4 => some .raw
    | .work3 => some .width
    | .work2 => some .counter
    | .work7 => some .backup
    | .work5 => some .output
    | _ => none
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k <;> cases k' <;> simp_all

def paddingWrapperLens {N : Nat} :
    StateLens PaddingControl (FullInterpreterState N) where
  get s := ⟨(FullInterpreterState.moveLens.get s).held, !s.lookupFound⟩
  put s c := FullInterpreterState.moveLens.put
    {s with lookupFound := !c.more} ⟨c.held⟩
  get_put := by
    intro s c
    rcases c with ⟨held, more⟩
    cases more <;> rfl
  put_get := by
    intro s
    cases s with
    | mk macros dispatch literal lookupFound subtractForceZero countdown =>
        cases lookupFound <;> rfl
  put_put := by
    intros
    simp [FullInterpreterState.moveLens, InterpreterMacroState.moveLens,
      FullInterpreterState.macroLens, StateLens.comp]

def finalizeInputWrapperRenaming :
    StackRenaming FinalizeInputStack CoreStack where
  encode
    | .source => .work5
    | .input => .input
  decode
    | .work5 => some .source
    | .input => some .input
    | _ => none
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k <;> cases k' <;> simp_all

def physicalRawCoreProgram {N : Nat} : Sum PhysicalRawLabel Unit →
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (Sum PhysicalRawLabel Unit)
      (FullInterpreterState N) :=
  lensSpliceProgram physicalRawWrapperRenaming moveWrapperLens
    physicalRawProgram .done () (fun _ => .halt)

def paddingCoreProgram {N : Nat} : Sum PaddingLabel Unit →
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (Sum PaddingLabel Unit)
      (FullInterpreterState N) :=
  lensSpliceProgram paddingWrapperRenaming paddingWrapperLens
    paddingProgram .done () (fun _ => .halt)

def finalizeInputCoreProgram {N : Nat} : Sum FinalizeInputLabel Unit →
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (Sum FinalizeInputLabel Unit)
      (FullInterpreterState N) :=
  lensSpliceProgram finalizeInputWrapperRenaming moveWrapperLens
    finalizeInputProgram .done () (fun _ => .halt)

def collapseEmptyLabel {L : Type} : Sum L Empty → L
  | .inl label => label
  | .inr impossible => nomatch impossible

def liftCoreProgramSame {N : Nat} {L : Type}
    (program : L → TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)) :
    L → TM2.Stmt WrapperAlphabet L (WrapperState N) :=
  fun label => mapLabelStmt collapseEmptyLabel
    (liftCoreStmt (X := Empty) (program label))

def liftCoreCfgSame {N : Nat} {L : Type}
    (cfg : TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (ambient : WrapperState N) (input output : List Symbol) :
    TM2.Cfg WrapperAlphabet L (WrapperState N) :=
  mapLabelCfg collapseEmptyLabel
    (liftCoreCfg (X := Empty) cfg ambient input output)

theorem iterate_liftCoreProgramSame {N n : Nat} {L : Type}
    (program : L → TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (ambient : WrapperState N) (input output : List Symbol)
    (hrun : ((fun o => o.bind (TM2.step program))^[n]) (some c) = some d) :
    ((fun o => o.bind (TM2.step (liftCoreProgramSame program)))^[n])
      (some (liftCoreCfgSame c ambient input output)) =
    some (liftCoreCfgSame d ambient input output) := by
  have hlift := iterate_liftCoreProgram program
    (fun impossible : Empty => nomatch impossible) c d ambient input output hrun
  have hmap := iterate_mapLabelProgram
    (liftCoreProgram program (fun impossible : Empty => nomatch impossible))
    (liftCoreProgramSame program) collapseEmptyLabel (by
      intro label
      cases label with
      | inl label => rfl
      | inr impossible => nomatch impossible)
    n (liftCoreCfg (X := Empty) c ambient input output)
  rw [hlift] at hmap
  exact hmap

def physicalRawWrapperProgram {N : Nat} :=
  liftCoreProgramSame (physicalRawCoreProgram (N := N))

def paddingWrapperProgram {N : Nat} :=
  liftCoreProgramSame (paddingCoreProgram (N := N))

def finalizeInputWrapperProgram {N : Nat} :=
  liftCoreProgramSame (finalizeInputCoreProgram (N := N))

theorem physicalRaw_wrapper_correct {N : Nat} (w : Nat) (x : List Nat)
    (state : WrapperState N)
    (ambient : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step physicalRawWrapperProgram))^[
        bitSize x + 2 * w + 5])
      (some (liftCoreCfgSame
        (lensRenamedCfg physicalRawWrapperRenaming moveWrapperLens
        (physicalRawCfg .reverseSaved
          ((encode x).reverse.map sparseOfInputSymbol) []
          ((fixedBits w x.length).map SparseSymbol.bit) []) state.core
          (fun k => ambient (.core k))) state (ambient .input) (ambient .output))) =
    some (liftCoreCfgSame
      (lensReturnCfg physicalRawWrapperRenaming moveWrapperLens ()
        (physicalRawCfg .done [] (physicalPaddingRaw w x) [] []) state.core
        (fun k => ambient (.core k))) state (ambient .input) (ambient .output)) := by
  have hcore := transport_lensHaltingMacro_and_return physicalRawWrapperRenaming
    moveWrapperLens physicalRawProgram .done (by rfl) () (fun _ => .halt)
    (physicalRaw_input_correct w x) rfl state.core (fun k => ambient (.core k))
  exact iterate_liftCoreProgramSame physicalRawCoreProgram _ _ state
    (ambient .input) (ambient .output) hcore

theorem padding_wrapper_correct {N : Nat} (w : Nat) (x : List Nat)
    (hlen : x.length < 2 ^ w) (hfit : ∀ n ∈ x, n < 2 ^ w)
    (state : WrapperState N)
    (ambient : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step paddingWrapperProgram))^[
        1 + (x.length + 1) * (3 * w + 5) + 1])
      (some (liftCoreCfgSame
        (lensRenamedCfg paddingWrapperRenaming paddingWrapperLens
        (paddingCfg .start default (physicalPaddingRaw w x)
          (unaryMarkers w) [] [] []) state.core (fun k => ambient (.core k)))
          state (ambient .input) (ambient .output))) =
    some (liftCoreCfgSame
      (lensReturnCfg paddingWrapperRenaming paddingWrapperLens ()
      (paddingCfg .done default [] (unaryMarkers w) [] []
        (encodeWordList w (x.length :: x)).reverse) state.core
        (fun k => ambient (.core k))) state (ambient .input) (ambient .output)) := by
  have hcore := transport_lensHaltingMacro_and_return paddingWrapperRenaming
    paddingWrapperLens paddingProgram .done (by rfl) () (fun _ => .halt)
    (padding_physical_input w x hlen hfit) rfl state.core
    (fun k => ambient (.core k))
  exact iterate_liftCoreProgramSame paddingCoreProgram _ _ state
    (ambient .input) (ambient .output) hcore

theorem finalizeInput_wrapper_correct {N : Nat} (w : Nat) (xs : List Nat)
    (state : WrapperState N)
    (ambient : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step finalizeInputWrapperProgram))^[
        (encodeWordList w xs).length + 4])
      (some (liftCoreCfgSame
        (lensRenamedCfg finalizeInputWrapperRenaming moveWrapperLens
          (finalizeInputCfg .mark (encodeWordList w xs).reverse []) state.core
          (fun k => ambient (.core k))) state (ambient .input) (ambient .output))) =
    some (liftCoreCfgSame
      (lensReturnCfg finalizeInputWrapperRenaming moveWrapperLens ()
        (finalizeInputCfg .done [] (encodeInputStack w xs)) state.core
        (fun k => ambient (.core k))) state (ambient .input) (ambient .output)) := by
  have hcore := transport_lensHaltingMacro_and_return finalizeInputWrapperRenaming
    moveWrapperLens finalizeInputProgram .done (by rfl) () (fun _ => .halt)
    (finalizeInput_encoded w xs) rfl state.core (fun k => ambient (.core k))
  exact iterate_liftCoreProgramSame finalizeInputCoreProgram _ _ state
    (ambient .input) (ambient .output) hcore

end

end Lax20Proofs.RamToTM
