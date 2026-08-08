import Lax20Proofs.RamToTM.UnaryPowerMacro

namespace Lax20Proofs.RamToTM

open Turing TM2
open Polynomial
open Lax20.BinaryWordEncoding Lax20.RamPolytime

noncomputable section

def unaryPowerWrapperRenaming : StackRenaming UnaryMulStack WrapperStack where
  encode k := .core (unaryMulCoreRenaming.encode k)
  decode
    | .core k => unaryMulCoreRenaming.decode k
    | _ => none
  decode_encode := unaryMulCoreRenaming.decode_encode
  encode_decode := by
    intro k' k h
    cases k' with
    | input => simp at h
    | output => simp at h
    | core k' =>
        simp only at h ⊢
        exact congrArg WrapperStack.core (unaryMulCoreRenaming.encode_decode h)

def unaryPowerWrapperLens {N : Nat} :
    StateLens SymbolMoveControl (WrapperState N) :=
  StateLens.comp FullInterpreterState.moveLens WrapperState.coreLens

def pushUnaryMarkers {N : Nat} {L : Type} (stack : CoreStack) : Nat →
    TM2.Stmt WrapperAlphabet L (WrapperState N) →
      TM2.Stmt WrapperAlphabet L (WrapperState N)
  | 0, q => q
  | n + 1, q => .push (.core stack) (fun _ => .wordEnd)
      (pushUnaryMarkers stack n q)

theorem stepAux_pushUnaryMarkers_work3 {N : Nat} {L : Type}
    (n : Nat) (q : TM2.Stmt WrapperAlphabet L (WrapperState N))
    (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.stepAux (pushUnaryMarkers .work3 n q) state tapes =
      TM2.stepAux q state (Function.update tapes (.core .work3)
        (List.replicate n SparseSymbol.wordEnd ++
          (show List SparseSymbol from tapes (.core .work3)))) := by
  induction n generalizing tapes with
  | zero => simp [pushUnaryMarkers, update_same_value]
  | succ n ih =>
      simp only [pushUnaryMarkers, TM2.stepAux]
      rw [ih]
      simp only [Function.update_self]
      have hlist : List.replicate n SparseSymbol.wordEnd ++
          (SparseSymbol.wordEnd ::
            (show List SparseSymbol from tapes (.core .work3))) =
          List.replicate (n + 1) SparseSymbol.wordEnd ++
            (show List SparseSymbol from tapes (.core .work3)) := by
        change List.replicate n SparseSymbol.wordEnd ++
            (List.replicate 1 SparseSymbol.wordEnd ++
              (show List SparseSymbol from tapes (.core .work3))) = _
        rw [← List.append_assoc, ← List.replicate_add]
      have heq :
          Function.update
              (Function.update tapes (.core .work3)
                (.wordEnd :: tapes (.core .work3)))
              (.core .work3)
              (List.replicate n .wordEnd ++
                (.wordEnd :: tapes (.core .work3))) =
            Function.update tapes (.core .work3)
              (List.replicate (n + 1) .wordEnd ++ tapes (.core .work3)) := by
        funext k
        cases k with
        | input | output => simp [Function.update]
        | core k =>
            cases k <;> simp [Function.update]
            exact hlist
      exact congrArg (TM2.stepAux q state) heq

inductive WidthBoundaryLabel | addOne | ready
  deriving DecidableEq, Fintype, Inhabited

abbrev InputWidthLabel (p : Polynomial Nat) :=
  Sum InputScanLabel (Sum (UnaryPowerLabel p.natDegree) WidthBoundaryLabel)

def widthBoundaryCoreProgram {N : Nat} {d : Nat} : WidthBoundaryLabel →
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum (UnaryPowerLabel d) WidthBoundaryLabel) (FullInterpreterState N)
  | .addOne =>
      .push .work3 (fun _ => .wordEnd) <|
      .goto fun _ => .inr .ready
  | .ready => .halt

def widthPowerCoreSpliceProgram {N : Nat} (p : Polynomial Nat) :=
  lensSpliceProgram unaryMulCoreRenaming FullInterpreterState.moveLens
    (unaryPowerProgram p.natDegree) (unaryPowerFinish p.natDegree)
    WidthBoundaryLabel.addOne (widthBoundaryCoreProgram (N := N))

def embedLiftedWidthPowerLabel {p : Polynomial Nat} :
    Sum (Sum (UnaryPowerLabel p.natDegree) WidthBoundaryLabel) Empty →
      InputWidthLabel p
  | .inl (.inl label) => .inr (.inl label)
  | .inl (.inr label) => .inr (.inr label)
  | .inr impossible => nomatch impossible

def inputWidthProgram {N : Nat} (p : Polynomial Nat) :
    InputWidthLabel p → TM2.Stmt WrapperAlphabet (InputWidthLabel p) (WrapperState N)
  | .inl .done =>
      .load (fun s => unaryPowerWrapperLens.put s default) <|
      .push (.core .work1) (fun _ => .wordEnd) <|
      pushUnaryMarkers .work3 (polyCoeffSum p) <|
      .goto fun _ => .inr (.inl (unaryPowerStart p.natDegree))
  | .inl label =>
      mapLabelStmt
        (fun label : Sum Empty InputScanLabel => match label with
          | Sum.inl impossible => nomatch impossible
          | Sum.inr next => Sum.inl next)
        (inputScanProgram (N := N) (L := Empty) label)
  | .inr label =>
      mapLabelStmt (embedLiftedWidthPowerLabel (p := p)) <|
        liftCoreStmt (N := N) (X := Empty) (widthPowerCoreSpliceProgram p label)

def inputWidthCfg {N : Nat} {p : Polynomial Nat} (label : InputWidthLabel p)
    (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.Cfg WrapperAlphabet (InputWidthLabel p) (WrapperState N) :=
  ⟨some label, state, tapes⟩

theorem inputWidth_scan_bridge {N : Nat} (p : Polynomial Nat)
    (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.step (inputWidthProgram p)
      (inputWidthCfg (.inl .done) state tapes) =
    some (inputWidthCfg (.inr (.inl (unaryPowerStart p.natDegree)))
      (unaryPowerWrapperLens.put state default)
      (Function.update
        (Function.update tapes (.core .work1)
          (.wordEnd :: tapes (.core .work1)))
        (.core .work3)
          (unaryMarkers (polyCoeffSum p) ++
            (show List SparseSymbol from tapes (.core .work3))))) := by
  simp only [inputWidthCfg, TM2.step, inputWidthProgram, TM2.stepAux]
  rw [stepAux_pushUnaryMarkers_work3]
  simp [unaryMarkers]

def embedWidthPowerLabel {p : Polynomial Nat} :
    Sum (UnaryPowerLabel p.natDegree) WidthBoundaryLabel → InputWidthLabel p
  | .inl label => .inr (.inl label)
  | .inr label => .inr (.inr label)

theorem inputWidth_power_run {N : Nat} (p : Polynomial Nat) (n : Nat)
    (ambientState : WrapperState N)
    (ambientStacks : (k : WrapperStack) → List (WrapperAlphabet k)) :
    ((fun o => o.bind (TM2.step (inputWidthProgram p)))^[
        (simpleMajorantEvalCostPolynomial p).eval n + 1])
      (some (mapLabelCfg (embedLiftedWidthPowerLabel (p := p))
        (liftCoreCfg (X := Empty)
          (lensRenamedCfg unaryMulCoreRenaming FullInterpreterState.moveLens
            (unaryPowerCfg (unaryPowerStart p.natDegree)
              (unaryMarkers (polyCoeffSum p)) (unaryMarkers (n + 1)) [] [])
            ambientState.core (fun k => ambientStacks (.core k)))
          ambientState (ambientStacks .input) (ambientStacks .output)))) =
    some (mapLabelCfg (embedLiftedWidthPowerLabel (p := p))
      (liftCoreCfg (X := Empty)
        (lensReturnCfg unaryMulCoreRenaming FullInterpreterState.moveLens
          WidthBoundaryLabel.addOne
          (unaryPowerCfg (unaryPowerFinish p.natDegree)
            (unaryMarkers ((polynomialSimpleMajorant p).eval n))
            (unaryMarkers (n + 1)) [] [])
          ambientState.core (fun k => ambientStacks (.core k)))
        ambientState (ambientStacks .input) (ambientStacks .output))) := by
  have hcore := unaryPower_core_simpleMajorant_correct (N := N) p n
    WidthBoundaryLabel.addOne (widthBoundaryCoreProgram (N := N))
    ambientState.core (fun k => ambientStacks (.core k))
  have hlift := iterate_liftCoreProgram
    (widthPowerCoreSpliceProgram (N := N) p)
    (fun impossible : Empty => nomatch impossible) _ _ ambientState
    (ambientStacks .input) (ambientStacks .output) hcore
  have hembed := iterate_mapLabelProgram
    (liftCoreProgram (widthPowerCoreSpliceProgram (N := N) p)
      (fun impossible : Empty => nomatch impossible))
    (inputWidthProgram p) (embedLiftedWidthPowerLabel (p := p))
    (fun label => by cases label with
      | inl label => cases label <;> rfl
      | inr impossible => nomatch impossible)
    ((simpleMajorantEvalCostPolynomial p).eval n + 1)
    (liftCoreCfg (X := Empty)
      (lensRenamedCfg unaryMulCoreRenaming FullInterpreterState.moveLens
        (unaryPowerCfg (unaryPowerStart p.natDegree)
          (unaryMarkers (polyCoeffSum p)) (unaryMarkers (n + 1)) [] [])
        ambientState.core (fun k => ambientStacks (.core k)))
      ambientState (ambientStacks .input) (ambientStacks .output))
  rw [hlift] at hembed
  exact hembed

def inputWidthInitialStacks (input : List Symbol) :
    (k : WrapperStack) → List (WrapperAlphabet k)
  | .input => input
  | .output => []
  | .core _ => []

def inputWidthScannedStacks (input : List Symbol) :
    (k : WrapperStack) → List (WrapperAlphabet k)
  | .input => []
  | .output => []
  | .core .work0 => input.reverse.map sparseOfInputSymbol
  | .core .work1 => List.replicate input.length .wordEnd
  | .core .work2 => List.replicate (inputSeparatorCount input) .wordEnd
  | .core _ => []

theorem inputScanStacks_initial (input : List Symbol) :
    inputScanStacks input [] (inputWidthInitialStacks input) =
      inputWidthInitialStacks input := by
  funext k
  cases k with
  | input => simp [inputScanStacks, inputWidthInitialStacks]
  | output => simp [inputScanStacks, inputWidthInitialStacks]
  | core k => cases k <;> simp [inputScanStacks, inputWidthInitialStacks]
    <;> rfl

theorem inputScanStacks_scanned (input : List Symbol) :
    inputScanStacks [] input (inputWidthInitialStacks input) =
      inputWidthScannedStacks input := by
  have hzero : inputSeparatorCount [] = 0 := rfl
  funext k
  cases k with
  | input => simp [inputScanStacks, inputWidthInitialStacks,
      inputWidthScannedStacks]; rfl
  | output => simp [inputScanStacks, inputWidthInitialStacks,
      inputWidthScannedStacks]
  | core k => cases k <;> simp [inputScanStacks, inputWidthInitialStacks,
      inputWidthScannedStacks, hzero]
    <;> rfl

theorem inputWidth_scan_bridge_powerStart {N : Nat} (p : Polynomial Nat)
    (input : List Symbol) (n : Nat) (hlen : input.length = n)
    (state : WrapperState N) :
    TM2.step (inputWidthProgram p)
      (inputWidthCfg (.inl .done) state (inputWidthScannedStacks input)) =
    some (mapLabelCfg (embedLiftedWidthPowerLabel (p := p))
      (liftCoreCfg (X := Empty)
        (lensRenamedCfg unaryMulCoreRenaming FullInterpreterState.moveLens
          (unaryPowerCfg (unaryPowerStart p.natDegree)
            (unaryMarkers (polyCoeffSum p)) (unaryMarkers (n + 1)) [] [])
          state.core (fun k => inputWidthScannedStacks input (.core k)))
        state (inputWidthScannedStacks input .input)
          (inputWidthScannedStacks input .output))) := by
  have h := inputWidth_scan_bridge (N := N) p state
    (inputWidthScannedStacks input)
  convert h using 1 <;>
    simp [inputWidthCfg, mapLabelCfg, liftCoreCfg, lensRenamedCfg,
      unaryMulCoreRenaming, unaryMulStacks, unaryPowerWrapperLens,
      unaryPowerCfg, embedLiftedWidthPowerLabel, WrapperState.coreLens,
      StateLens.comp, inputWidthScannedStacks, unaryMarkers, hlen,
      List.replicate_succ]
  funext k
  cases k with
  | input | output => rfl
  | core k =>
      cases k <;> simp [renamedStacks, unaryMulCoreRenaming,
        unaryMulStacks, inputWidthScannedStacks, wrapperCoreStacks,
        Function.update, List.append_nil] <;>
        first | exact rfl | exact (List.append_nil _).symm

def embedInputScanLabel {p : Polynomial Nat} :
    Sum Empty InputScanLabel → InputWidthLabel p
  | .inl impossible => nomatch impossible
  | .inr label => .inl label

theorem inputWidth_scan_run {N : Nat} (p : Polynomial Nat)
    (input : List Symbol) (state : WrapperState N) :
    ((fun o => o.bind (TM2.step (inputWidthProgram p)))^[4 * input.length + 2])
      (some (inputWidthCfg (.inl .scan) {state with heldInput := none}
        (inputWidthInitialStacks input))) =
    some (inputWidthCfg (.inl .done) {state with heldInput := none}
      (inputWidthScannedStacks input)) := by
  have hrun := input_scan_all (N := N) input state
    (inputWidthInitialStacks input)
  rw [inputScanStacks_initial, inputScanStacks_scanned] at hrun
  apply iterate_mapLabelProgram_until_exit inputScanMachine
    (inputWidthProgram p) embedInputScanLabel
    (fun label hnonhalt => by
      cases label with
      | inl impossible => nomatch impossible
      | inr label =>
          cases label <;>
            simp [inputScanMachine, liftCoreProgram, inputScanProgram,
              embedInputScanLabel, inputWidthProgram, mapLabelStmt] at hnonhalt ⊢)
    hrun
  rfl

theorem inputWidth_addOne_step {N : Nat} (p : Polynomial Nat)
    (state : WrapperState N)
    (tapes : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.step (inputWidthProgram p)
      (inputWidthCfg (.inr (.inr .addOne)) state tapes) =
    some (inputWidthCfg (.inr (.inr .ready)) state
      (Function.update tapes (.core .work3)
        (.wordEnd :: tapes (.core .work3)))) := by
  simp [inputWidthCfg, inputWidthProgram, widthPowerCoreSpliceProgram,
    lensSpliceProgram, widthBoundaryCoreProgram, liftCoreStmt,
    mapLabelStmt, embedLiftedWidthPowerLabel, TM2.step]

def inputWidthPowerFinalCfg {N : Nat} (p : Polynomial Nat) (n : Nat)
    (ambientState : WrapperState N)
    (ambientStacks : (k : WrapperStack) → List (WrapperAlphabet k)) :=
  mapLabelCfg (embedLiftedWidthPowerLabel (p := p)) <|
    liftCoreCfg (X := Empty)
      (lensReturnCfg unaryMulCoreRenaming FullInterpreterState.moveLens
        WidthBoundaryLabel.addOne
        (unaryPowerCfg (unaryPowerFinish p.natDegree)
          (unaryMarkers ((polynomialSimpleMajorant p).eval n))
          (unaryMarkers (n + 1)) [] [])
        ambientState.core (fun k => ambientStacks (.core k)))
      ambientState (ambientStacks .input) (ambientStacks .output)

def inputWidthReadyCfg {N : Nat} (p : Polynomial Nat) (n : Nat)
    (ambientState : WrapperState N)
    (ambientStacks : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.Cfg WrapperAlphabet (InputWidthLabel p) (WrapperState N) :=
  let c := inputWidthPowerFinalCfg p n ambientState ambientStacks
  { c with
    l := some (.inr (.inr .ready))
    stk := Function.update c.stk (.core .work3)
      (.wordEnd :: c.stk (.core .work3)) }

theorem inputWidth_power_addOne {N : Nat} (p : Polynomial Nat) (n : Nat)
    (ambientState : WrapperState N)
    (ambientStacks : (k : WrapperStack) → List (WrapperAlphabet k)) :
    TM2.step (inputWidthProgram p)
      (inputWidthPowerFinalCfg p n ambientState ambientStacks) =
    some (inputWidthReadyCfg p n ambientState ambientStacks) := by
  let c := inputWidthPowerFinalCfg p n ambientState ambientStacks
  have hc : c.l = some (.inr (.inr .addOne)) := by
    simp [c, inputWidthPowerFinalCfg, mapLabelCfg, liftCoreCfg,
      lensReturnCfg, embedLiftedWidthPowerLabel]
  have heq : c = inputWidthCfg (.inr (.inr .addOne)) c.var c.stk := by
    cases hcfg : c with
    | mk l v s =>
        have hl : l = some (.inr (.inr .addOne)) := by
          simpa [hcfg] using hc
        subst l
        rfl
  have hadd := inputWidth_addOne_step p c.var c.stk
  rw [← heq] at hadd
  change TM2.step (inputWidthProgram p) c = some
    { c with
      l := some (.inr (.inr .ready))
      stk := Function.update c.stk (.core .work3)
        (.wordEnd :: c.stk (.core .work3)) }
  exact hadd

theorem inputWidth_complete_run {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    ((fun o => o.bind (TM2.step (inputWidthProgram p)))^[
        4 * bitSize x + (simpleMajorantEvalCostPolynomial p).eval (bitSize x) + 5])
      (some (inputWidthCfg (.inl .scan) {state with heldInput := none}
        (inputWidthInitialStacks (encode x)))) =
    some (inputWidthReadyCfg p (bitSize x)
      {state with heldInput := none} (inputWidthScannedStacks (encode x))) := by
  have hscan := inputWidth_scan_run (N := N) p (encode x) state
  have hbridge := inputWidth_scan_bridge_powerStart (N := N) p
    (encode x) (bitSize x) (by simp [bitSize]) {state with heldInput := none}
  have hpower := inputWidth_power_run (N := N) p (bitSize x)
    {state with heldInput := none} (inputWidthScannedStacks (encode x))
  have hadd := inputWidth_power_addOne (N := N) p (bitSize x)
    {state with heldInput := none} (inputWidthScannedStacks (encode x))
  have liftStep {a b : TM2.Cfg WrapperAlphabet (InputWidthLabel p)
      (WrapperState N)} (hs : TM2.step (inputWidthProgram p) a = some b) :
      ((fun o => o.bind (TM2.step (inputWidthProgram p)))^[1])
        (some a) = some b := by
    simpa
  have hbridge' := liftStep hbridge
  have hadd' := liftStep hadd
  have hbridgePower := chain_iterations _ hbridge' hpower
  have htail := chain_iterations _ hbridgePower hadd'
  have h := chain_iterations _ hscan htail
  rw [simpleMajorantEvalCostPolynomial_eval] at h
  rw [show (4 * (encode x).length + 2) +
      (1 + (unaryPowerCost (polyCoeffSum p) (bitSize x + 1)
        p.natDegree + 1) + 1) =
      4 * (encode x).length +
        unaryPowerCost (polyCoeffSum p) (bitSize x + 1)
          p.natDegree + 5 by omega] at h
  simpa only [bitSize, simpleMajorantEvalCostPolynomial_eval] using h

@[simp] theorem inputWidthReadyCfg_work0 {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    (inputWidthReadyCfg p (bitSize x) state
      (inputWidthScannedStacks (encode x))).stk (.core .work0) =
      (encode x).reverse.map sparseOfInputSymbol := by
  simp [inputWidthReadyCfg, inputWidthPowerFinalCfg, mapLabelCfg,
    liftCoreCfg, wrapperCoreStacks, lensReturnCfg, lensRenamedCfg,
    renamedStacks, unaryMulCoreRenaming, unaryMulStacks,
    unaryPowerCfg, inputWidthScannedStacks, Function.update] <;> rfl

@[simp] theorem inputWidthReadyCfg_work1 {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    (inputWidthReadyCfg p (bitSize x) state
      (inputWidthScannedStacks (encode x))).stk (.core .work1) =
      unaryMarkers (bitSize x + 1) := by
  simp [inputWidthReadyCfg, inputWidthPowerFinalCfg, mapLabelCfg,
    liftCoreCfg, wrapperCoreStacks, lensReturnCfg, lensRenamedCfg,
    renamedStacks, unaryMulCoreRenaming, unaryMulStacks,
    unaryPowerCfg, inputWidthScannedStacks, Function.update] <;> rfl

@[simp] theorem inputWidthReadyCfg_work2 {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    (inputWidthReadyCfg p (bitSize x) state
      (inputWidthScannedStacks (encode x))).stk (.core .work2) =
      unaryMarkers x.length := by
  simp [inputWidthReadyCfg, inputWidthPowerFinalCfg, mapLabelCfg,
    liftCoreCfg, wrapperCoreStacks, lensReturnCfg, lensRenamedCfg,
    renamedStacks, unaryMulCoreRenaming, unaryMulStacks,
    unaryPowerCfg, inputWidthScannedStacks, unaryMarkers,
    inputSeparatorCount_encode, Function.update] <;> rfl

@[simp] theorem inputWidthReadyCfg_work3 {N : Nat} (p : Polynomial Nat)
    (x : List Nat) (state : WrapperState N) :
    (inputWidthReadyCfg p (bitSize x) state
      (inputWidthScannedStacks (encode x))).stk (.core .work3) =
      unaryMarkers (simulationWordWidth p x) := by
  simp [inputWidthReadyCfg, inputWidthPowerFinalCfg, mapLabelCfg,
    liftCoreCfg, wrapperCoreStacks, lensReturnCfg, lensRenamedCfg,
    renamedStacks, unaryMulCoreRenaming, unaryMulStacks,
    unaryPowerCfg, inputWidthScannedStacks, unaryMarkers,
    simulationWordWidth, List.replicate_succ, Function.update] <;> rfl

end

end Lax20Proofs.RamToTM
