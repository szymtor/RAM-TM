import Lax51Proofs.RamToTM.CappedShiftCorrect
import Lax51Proofs.RamToTM.FullCopyMacro
import Lax51Proofs.RamToTM.ConditionalAccumulatorZeroPhase
import Lax51Proofs.RamToTM.LiteralPreservation

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

inductive ShiftSetupLabel
  | initialize
  | move (label : SymbolMoveLabel)
  | copy (label : CopyLabel)
  | controller (label : CappedShiftLabel)
  deriving DecidableEq, Fintype, Inhabited

def embedSetupMove : Sum SymbolMoveLabel Unit -> ShiftSetupLabel
  | .inl label => .move label
  | .inr () => .copy .scan

def embedSetupCopy : Sum CopyLabel Unit -> ShiftSetupLabel
  | .inl label => .copy label
  | .inr () => .controller (.countdown .scan)

def shiftSetupProgram {N : Nat} (rightShift : Bool) :
    ShiftSetupLabel -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) ShiftSetupLabel
      (FullInterpreterState N)
  | .initialize =>
      .load resetShiftControls <| .goto fun _ => .move .loop
  | .move label =>
      mapLabelStmt embedSetupMove <|
        lensPhaseLeft
          (symbolMoveCoreRenaming .work0 .work3 (by decide))
          FullInterpreterState.moveLens symbolMoveCoreProgram .done () label
  | .copy label =>
      mapLabelStmt embedSetupCopy <|
        lensPhaseLeft
          (copyCoreRenaming .accumulator .work1 .work7
            (by decide) (by decide) (by decide))
          FullInterpreterState.moveLens copyProgram .done () label
  | .controller label =>
      mapLabelStmt ShiftSetupLabel.controller
        (cappedShiftProgram rightShift label)

def shiftCountBase (w accumulator count : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) :
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 | .work1 | .work2 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def shiftSetupStartCfg {N : Nat} (state : FullInterpreterState N)
    (w accumulator count : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) ShiftSetupLabel
      (FullInterpreterState N) :=
  cleanReturnCfg .initialize state
    (operandResultBase w accumulator count m base)

def shiftSetupBound (w : Nat) : Nat := 3 * w + 6

def shiftSetupMoveSource {N : Nat} :
    Sum SymbolMoveLabel Unit -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (Sum SymbolMoveLabel Unit)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work3 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done ())
    (fun _ => .halt)

theorem shiftSetupMoveSource_embeds {N : Nat} (rightShift : Bool)
    (label : Sum SymbolMoveLabel Unit)
    (hn : shiftSetupMoveSource (N := N) label ≠ .halt) :
    shiftSetupProgram (N := N) rightShift (embedSetupMove label) =
      mapLabelStmt embedSetupMove (shiftSetupMoveSource label) := by
  cases label with
  | inl label => rfl
  | inr unit =>
      cases unit
      exact False.elim (hn rfl)

def shiftSetupCopySource {N : Nat} :
    Sum CopyLabel Unit -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (Sum CopyLabel Unit)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (copyCoreRenaming .accumulator .work1 .work7
        (by decide) (by decide) (by decide))
      FullInterpreterState.moveLens copyProgram .done ())
    (fun _ => .halt)

theorem shiftSetupCopySource_embeds {N : Nat} (rightShift : Bool)
    (label : Sum CopyLabel Unit)
    (hn : shiftSetupCopySource (N := N) label ≠ .halt) :
    shiftSetupProgram (N := N) rightShift (embedSetupCopy label) =
      mapLabelStmt embedSetupCopy (shiftSetupCopySource label) := by
  cases label with
  | inl label => rfl
  | inr unit =>
      cases unit
      exact False.elim (hn rfl)

theorem shiftSetup_initialize_step {N : Nat} (rightShift : Bool)
    (state : FullInterpreterState N) (w accumulator count : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    TM2.step (shiftSetupProgram rightShift)
      (shiftSetupStartCfg state w accumulator count m base) =
    some (cleanReturnCfg (.move .loop) (resetShiftControls state)
      (operandResultBase w accumulator count m base)) := by
  rfl

theorem shiftSetup_move_start_bridge {N : Nat}
    (state : FullInterpreterState N) (w accumulator count : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    mapLabelCfg embedSetupMove
      (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work3 (by decide))
        FullInterpreterState.moveLens
        (symbolMoveLocalCfg .loop
          ((fixedBits w count).reverse.map SparseSymbol.bit) [])
        state (operandResultBase w accumulator count m base)) =
    cleanReturnCfg (.move .loop)
      (FullInterpreterState.moveLens.put state default)
      (operandResultBase w accumulator count m base) := by
  simp [mapLabelCfg, lensRenamedCfg, symbolMoveLocalCfg, symbolMoveStacks,
    operandResultBase, cleanReturnCfg, renamedStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
      symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
      operandResultBase]

theorem shiftSetup_move_return_bridge {N : Nat}
    (state : FullInterpreterState N) (w accumulator count : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    mapLabelCfg embedSetupMove
      (mapLabelCfg Sum.inr
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work0 .work3 (by decide))
          FullInterpreterState.moveLens ()
          (symbolMoveLocalCfg .done []
            (((fixedBits w count).reverse.map SparseSymbol.bit).reverse))
          state (operandResultBase w accumulator count m base))) =
    cleanReturnCfg (.copy .scan)
      (FullInterpreterState.moveLens.put state default)
      (shiftCountBase w accumulator count m base) := by
  simp [mapLabelCfg, phaseReturnCfg, lensRenamedCfg, symbolMoveLocalCfg,
    symbolMoveStacks, operandResultBase, cleanReturnCfg, renamedStacks,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, shiftCountBase,
    List.map_reverse]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
      symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
      operandResultBase, shiftCountBase, List.map_reverse]

theorem shiftSetup_copy_start_bridge {N : Nat}
    (state : FullInterpreterState N) (w accumulator count : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    mapLabelCfg embedSetupCopy
      (lensRenamedCfg
        (copyCoreRenaming .accumulator .work1 .work7
          (by decide) (by decide) (by decide))
        FullInterpreterState.moveLens
        (copyCfg .scan ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        state (shiftCountBase w accumulator count m base)) =
    cleanReturnCfg (.copy .scan)
      (FullInterpreterState.moveLens.put state default)
      (shiftCountBase w accumulator count m base) := by
  simp [mapLabelCfg, lensRenamedCfg, copyCfg, copyCfgState, copyStacks,
    cleanReturnCfg, renamedStacks, copyCoreRenaming, shiftCountBase]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks, copyCoreRenaming, copyCfg,
      copyCfgState, copyStacks, shiftCountBase]

theorem shiftSetup_copy_return_bridge {N : Nat}
    (state : FullInterpreterState N) (w accumulator count : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    mapLabelCfg embedSetupCopy
      (mapLabelCfg Sum.inr
        (cleanReturnCfg () state
          (copyAccumulatorStacks
            ((fixedBits w accumulator).map SparseSymbol.bit)
            (shiftCountBase w accumulator count m base)))) =
    cleanReturnCfg (.controller (.countdown .scan)) state
      (shiftRoundBase w accumulator count
        (((fixedBits w accumulator).map SparseSymbol.bit).reverse)
        m base) := by
  simp [mapLabelCfg, cleanReturnCfg]
  constructor
  · rfl
  · funext k
    cases k <;> simp [copyAccumulatorStacks, shiftCountBase, shiftRoundBase]

theorem shiftSetupController_embeds {N : Nat} (rightShift : Bool)
    (label : CappedShiftLabel) :
    shiftSetupProgram (N := N) rightShift (.controller label) =
      mapLabelStmt ShiftSetupLabel.controller
        (cappedShiftProgram rightShift label) := by
  rfl

theorem shiftSetup_correct {N : Nat} (rightShift : Bool)
    (state : FullInterpreterState N) (w accumulator count : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    ((fun x => x.bind (TM2.step (shiftSetupProgram rightShift)))^[
        shiftSetupBound w])
      (some (shiftSetupStartCfg state w accumulator count m base)) =
    some (cleanReturnCfg (.controller (.countdown .scan))
      (resetShiftControls state)
      (shiftRoundBase w accumulator count
        (((fixedBits w accumulator).map SparseSymbol.bit).reverse)
        m base)) := by
  let resetState := resetShiftControls state
  have hinit := shiftSetup_initialize_step rightShift state w accumulator count
    m base
  let countBits := (fixedBits w count).reverse.map SparseSymbol.bit
  have hmoveLocal := symbolMoveLocal_correct countBits []
  have hmoveSource := run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .work3 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl) ()
    (fun _ : Unit => .halt) hmoveLocal rfl resetState
    (operandResultBase w accumulator count m base)
  have hmove := iterate_mapLabelProgram_until_exit
    shiftSetupMoveSource (shiftSetupProgram rightShift) embedSetupMove
    (shiftSetupMoveSource_embeds rightShift) hmoveSource (by rfl)
  dsimp [countBits] at hmove
  simp only [List.length_map, List.length_reverse, fixedBits_length,
    List.append_nil] at hmove
  rw [shiftSetup_move_start_bridge resetState w accumulator count m base]
    at hmove
  rw [show FullInterpreterState.moveLens.put resetState default = resetState by
      rw [← resetShiftControls_move state]
      exact FullInterpreterState.moveLens.put_get resetState] at hmove
  rw [shiftSetup_move_return_bridge resetState w accumulator count m base]
    at hmove
  have hresetMove : FullInterpreterState.moveLens.put resetState default =
      resetState := by
    rw [← resetShiftControls_move state]
    exact FullInterpreterState.moveLens.put_get resetState
  rw [hresetMove] at hmove
  have hcopySource := fullCopyAccumulator_generic_correct ()
    (fun _ : Unit => .halt)
    ((fixedBits w accumulator).map SparseSymbol.bit)
    (shiftCountBase w accumulator count m base) resetState
  have hcopy := iterate_mapLabelProgram_until_exit
    shiftSetupCopySource (shiftSetupProgram rightShift) embedSetupCopy
    (shiftSetupCopySource_embeds rightShift) hcopySource (by rfl)
  rw [shiftSetup_copy_start_bridge resetState w accumulator count m base]
    at hcopy
  rw [show FullInterpreterState.moveLens.put resetState default = resetState by
      rw [← resetShiftControls_move state]
      exact FullInterpreterState.moveLens.put_get resetState] at hcopy
  rw [shiftSetup_copy_return_bridge resetState w accumulator count m base]
    at hcopy
  rw [show 2 * ((fixedBits w accumulator).map SparseSymbol.bit).length + 3 =
    2 * w + 3 by simp] at hcopy
  let stepO := fun x : Option (TM2.Cfg
      (fun _ : CoreStack => SparseSymbol) ShiftSetupLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (shiftSetupProgram rightShift))
  have hinit' : (stepO^[1])
      (some (shiftSetupStartCfg state w accumulator count m base)) =
      some (cleanReturnCfg (.move .loop) resetState
        (operandResultBase w accumulator count m base)) := by
    simpa [stepO, resetState] using hinit
  have hmove' : (stepO^[w + 2])
      (some (cleanReturnCfg (.move .loop) resetState
        (operandResultBase w accumulator count m base))) =
      some (cleanReturnCfg (.copy .scan) resetState
        (shiftCountBase w accumulator count m base)) := by
    rw [show w + 2 = Nat.succ (Nat.succ w) by omega,
      Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact hmove
  have h₁ := chain_iterations stepO hinit' hmove'
  have h₂ := chain_iterations stepO h₁ hcopy
  change (stepO^[shiftSetupBound w])
    (some (shiftSetupStartCfg state w accumulator count m base)) = _
  rw [show shiftSetupBound w = 1 + (w + 2) + (2 * w + 3) by
    simp [shiftSetupBound]; omega]
  exact h₂

theorem preservesLiteral_shiftSetupProgram {N : Nat}
    (rightShift : Bool) :
    ProgramPreservesLiteral (shiftSetupProgram (N := N) rightShift) := by
  intro label
  cases label with
  | «initialize» =>
      intro state tapes
      simp [shiftSetupProgram, TM2.stepAux, literal_resetShiftControls]
  | move label =>
      exact preservesLiteral_mapLabel embedSetupMove
        (lensPhaseLeft
          (symbolMoveCoreRenaming .work0 .work3 (by decide))
          FullInterpreterState.moveLens symbolMoveCoreProgram .done () label)
        (preservesLiteral_lensPhase
          (symbolMoveCoreRenaming .work0 .work3 (by decide))
          FullInterpreterState.moveLens literal_move_put
          symbolMoveCoreProgram .done () label)
  | copy label =>
      exact preservesLiteral_mapLabel embedSetupCopy
        (lensPhaseLeft
          (copyCoreRenaming .accumulator .work1 .work7
            (by decide) (by decide) (by decide))
          FullInterpreterState.moveLens copyProgram .done () label)
        (preservesLiteral_lensPhase
          (copyCoreRenaming .accumulator .work1 .work7
            (by decide) (by decide) (by decide))
          FullInterpreterState.moveLens literal_move_put
          copyProgram .done () label)
  | controller label =>
      exact preservesLiteral_mapLabel ShiftSetupLabel.controller
        (cappedShiftProgram rightShift label)
        (preservesLiteral_cappedShiftProgram rightShift label)

def shiftCoreBound (w : Nat) : Nat :=
  shiftSetupBound w + cappedShiftLoopBound w w

theorem shiftLeftCore_correct {N : Nat}
    (state : FullInterpreterState N) (w accumulator count : Nat)
    (hw : 0 < w) (hacc : accumulator < 2 ^ w)
    (hcount : count < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    ∃ steps, steps <= shiftCoreBound w ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step (shiftSetupProgram false)))^[steps])
        (some (shiftSetupStartCfg state w accumulator count m base)) =
      some (cleanReturnCfg (.controller .done) finalState
        (operandBoundaryBase w
          (cappedLeftValue w accumulator count w) m base)) := by
  have hsetup := shiftSetup_correct false state w accumulator count m base
  let resetState := resetShiftControls state
  let fuel := ((fixedBits w accumulator).map SparseSymbol.bit).reverse
  have hfuelLength : fuel.length = w := by
    simp [fuel]
  rcases cappedLeft_loop_correct w accumulator count hw hacc hcount fuel m base
      resetState (resetShiftControls_countdown state) with
    ⟨loopSteps, hloopBound, loopState, hloop⟩
  rw [hfuelLength] at hloopBound
  have hloopEmbedded := iterate_mapLabelProgram_until_exit
    (cappedShiftProgram false) (shiftSetupProgram false)
    ShiftSetupLabel.controller (fun label _ => shiftSetupController_embeds false label)
    hloop (by rfl)
  have hstart :
      mapLabelCfg ShiftSetupLabel.controller
        (cappedShiftCfg (.countdown .scan) resetState
          w accumulator count fuel m base) =
      cleanReturnCfg (.controller (.countdown .scan)) resetState
        (shiftRoundBase w accumulator count fuel m base) := by
    rfl
  rw [hstart] at hloopEmbedded
  have hend :
      mapLabelCfg ShiftSetupLabel.controller
        (controllerCfg .done loopState
          (operandBoundaryBase w
            (cappedLeftValue w accumulator count fuel.length) m base)) =
      cleanReturnCfg (.controller .done) loopState
        (operandBoundaryBase w
          (cappedLeftValue w accumulator count w) m base) := by
    simp [mapLabelCfg, controllerCfg, cleanReturnCfg, hfuelLength]
  rw [hend] at hloopEmbedded
  let stepO := fun x : Option (TM2.Cfg
      (fun _ : CoreStack => SparseSymbol) ShiftSetupLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (shiftSetupProgram false))
  have hall := chain_iterations stepO hsetup hloopEmbedded
  refine ⟨shiftSetupBound w + loopSteps, ?_, loopState, ?_⟩
  · simp [shiftCoreBound]
    omega
  · exact hall

theorem shiftRightCore_correct {N : Nat}
    (state : FullInterpreterState N) (w accumulator count : Nat)
    (hw : 0 < w) (hacc : accumulator < 2 ^ w)
    (hcount : count < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    ∃ steps, steps <= shiftCoreBound w ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step (shiftSetupProgram true)))^[steps])
        (some (shiftSetupStartCfg state w accumulator count m base)) =
      some (cleanReturnCfg (.controller .done) finalState
        (operandBoundaryBase w
          (cappedRightValue accumulator count w) m base)) := by
  have hsetup := shiftSetup_correct true state w accumulator count m base
  let resetState := resetShiftControls state
  let fuel := ((fixedBits w accumulator).map SparseSymbol.bit).reverse
  have hfuelLength : fuel.length = w := by
    simp [fuel]
  rcases cappedRight_loop_correct w accumulator count hw hacc hcount fuel m base
      resetState (resetShiftControls_countdown state) with
    ⟨loopSteps, hloopBound, loopState, hloop⟩
  rw [hfuelLength] at hloopBound
  have hloopEmbedded := iterate_mapLabelProgram_until_exit
    (cappedShiftProgram true) (shiftSetupProgram true)
    ShiftSetupLabel.controller (fun label _ => shiftSetupController_embeds true label)
    hloop (by rfl)
  have hstart :
      mapLabelCfg ShiftSetupLabel.controller
        (cappedShiftCfg (.countdown .scan) resetState
          w accumulator count fuel m base) =
      cleanReturnCfg (.controller (.countdown .scan)) resetState
        (shiftRoundBase w accumulator count fuel m base) := by
    rfl
  rw [hstart] at hloopEmbedded
  have hend :
      mapLabelCfg ShiftSetupLabel.controller
        (controllerCfg .done loopState
          (operandBoundaryBase w
            (cappedRightValue accumulator count fuel.length) m base)) =
      cleanReturnCfg (.controller .done) loopState
        (operandBoundaryBase w
          (cappedRightValue accumulator count w) m base) := by
    simp [mapLabelCfg, controllerCfg, cleanReturnCfg, hfuelLength]
  rw [hend] at hloopEmbedded
  let stepO := fun x : Option (TM2.Cfg
      (fun _ : CoreStack => SparseSymbol) ShiftSetupLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (shiftSetupProgram true))
  have hall := chain_iterations stepO hsetup hloopEmbedded
  refine ⟨shiftSetupBound w + loopSteps, ?_, loopState, ?_⟩
  · simp [shiftCoreBound]
    omega
  · exact hall

abbrev FullShiftLabel (R : Type) :=
  Sum ShiftSetupLabel (ConditionalZeroPhaseLabel R)

def fullShiftLeft {N : Nat} {R : Type} (rightShift : Bool) :
    ShiftSetupLabel -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullShiftLabel R)
      (FullInterpreterState N)
  | .controller .done =>
      .load (fun s => FullInterpreterState.moveLens.put s default) <|
        .goto fun _ => Sum.inr (Sum.inl ConditionalZeroLabel.rewrite)
  | label => mapLabelStmt Sum.inl (shiftSetupProgram rightShift label)

def fullShiftProgram {N : Nat} {R : Type} (o : Op) (rightShift : Bool)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullShiftLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullShiftLabel R)
      (FullInterpreterState N) :=
  liftRightProgram (fullShiftLeft (R := R) rightShift)
    (conditionalZeroPhaseProgram o returnLabel right)

theorem fullShiftLeft_embeds {N : Nat} {R : Type} (o : Op)
    (rightShift : Bool) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (label : ShiftSetupLabel)
    (hn : shiftSetupProgram (N := N) rightShift label ≠ .halt) :
    fullShiftProgram (N := N) o rightShift returnLabel right (Sum.inl label) =
      mapLabelStmt Sum.inl (shiftSetupProgram rightShift label) := by
  cases label with
  | «initialize» => rfl
  | move label => rfl
  | copy label => rfl
  | controller label =>
      cases label with
      | countdown label => rfl
      | fuel => rfl
      | left label => rfl
      | right label => rfl
      | cleanupFuel => rfl
      | cleanupCount => rfl
      | cleanupTemp => rfl
      | done => exact False.elim (hn rfl)

def fullShiftPostStartCfg {N : Nat} {R : Type}
    (state : FullInterpreterState N) (w value : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) (FullShiftLabel R)
      (FullInterpreterState N) :=
  mapLabelCfg Sum.inr <|
    lensRenamedCfg coreIdentityRenaming (fullStateIdentityLens N)
      (conditionalZeroCfg .rewrite state
        ((fixedBits w value).map SparseSymbol.bit) []
        (operandBoundaryBase w value m base))
      state (operandBoundaryBase w value m base)

theorem fullShift_to_post_step {N : Nat} {R : Type} (o : Op)
    (rightShift : Bool) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N) (w value : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    TM2.step (fullShiftProgram o rightShift returnLabel right)
      (mapLabelCfg Sum.inl
        (cleanReturnCfg (.controller .done) state
          (operandBoundaryBase w value m base))) =
    some (fullShiftPostStartCfg (R := R)
      (FullInterpreterState.moveLens.put state default)
      w value m base) := by
  simp [fullShiftProgram, liftRightProgram, fullShiftLeft,
    fullShiftPostStartCfg, mapLabelCfg, lensRenamedCfg,
    coreIdentityRenaming, renamedStacks_coreIdentity, fullStateIdentityLens,
    conditionalZeroCfg, cleanReturnCfg, TM2.step, TM2.stepAux]
  funext k
  cases k <;> simp [renamedStacks, coreIdentityRenaming,
    conditionalZeroCfg, operandBoundaryBase]

def fullShiftBound (w : Nat) : Nat := shiftCoreBound w + 2 * w + 5

theorem fullShift_finish {N : Nat} {R : Type} (o : Op)
    (rightShift : Bool) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N) (w accumulator count value : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (coreSteps : Nat) (hcoreBound : coreSteps <= shiftCoreBound w)
    (coreState : FullInterpreterState N)
    (hcore :
      ((fun x => x.bind (TM2.step (shiftSetupProgram rightShift)))^[coreSteps])
        (some (shiftSetupStartCfg state w accumulator count m base)) =
      some (cleanReturnCfg (.controller .done) coreState
        (operandBoundaryBase w value m base))) :
    ∃ steps, steps <= fullShiftBound w ∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (fullShiftProgram o rightShift returnLabel right)))^[steps])
        (some (mapLabelCfg Sum.inl
          (shiftSetupStartCfg state w accumulator count m base))) =
      some (mapLabelCfg Sum.inr
        (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                (if operandLiteralOversized o
                    (FullInterpreterState.moveLens.put coreState default)
                  then 0 else value) m base))))) := by
  have hcoreEmbedded := iterate_mapLabelProgram_until_exit
    (shiftSetupProgram rightShift)
    (fullShiftProgram o rightShift returnLabel right) Sum.inl
    (fullShiftLeft_embeds o rightShift returnLabel right) hcore (by rfl)
  let postState := FullInterpreterState.moveLens.put coreState default
  have htransition := fullShift_to_post_step o rightShift returnLabel right
    coreState w value m base
  rcases conditionalZeroPhase_correct o returnLabel right w value m base
      postState (FullInterpreterState.moveLens.get_put _ _) with
    ⟨finalState, hpost⟩
  have hpostLift := transport_iterate_liftRightProgram
    (fullShiftLeft (R := R) rightShift)
    (conditionalZeroPhaseProgram o returnLabel right) hpost
  let stepO := fun x : Option (TM2.Cfg
      (fun _ : CoreStack => SparseSymbol) (FullShiftLabel R)
      (FullInterpreterState N)) =>
    x.bind (TM2.step (fullShiftProgram o rightShift returnLabel right))
  have htransition' : (stepO^[1])
      (some (mapLabelCfg Sum.inl
        (cleanReturnCfg (.controller .done) coreState
          (operandBoundaryBase w value m base)))) =
      some (fullShiftPostStartCfg (R := R) postState w value m base) := by
    simpa [stepO, postState] using htransition
  have h₁ := chain_iterations stepO hcoreEmbedded htransition'
  have h₂ := chain_iterations stepO h₁ hpostLift
  refine ⟨coreSteps + 1 + (2 * w + 4), ?_, finalState, ?_⟩
  · simp [fullShiftBound]
    omega
  · simpa [stepO, fullShiftProgram, postState] using h₂

theorem operandLiteralOversized_eq_of_literal {N : Nat} (o : Op)
    (first second : FullInterpreterState N)
    (h : first.literal = second.literal) :
    operandLiteralOversized o first = operandLiteralOversized o second := by
  cases o with
  | lit n =>
      exact congrArg (fun value : BoundedLiteralControl N =>
        value.remaining.val != 0) h
  | mem n => rfl
  | ind n => rfl

theorem fullShiftLeft_correct {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N) (w accumulator count : Nat)
    (hw : 0 < w) (hacc : accumulator < 2 ^ w)
    (hcount : count < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    ∃ steps, steps <= fullShiftBound w ∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (fullShiftProgram o false returnLabel right)))^[steps])
        (some (mapLabelCfg Sum.inl
          (shiftSetupStartCfg state w accumulator count m base))) =
      some (mapLabelCfg Sum.inr
        (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                (if operandLiteralOversized o state
                  then 0 else cappedLeftValue w accumulator count w) m base))))) := by
  rcases shiftLeftCore_correct state w accumulator count hw hacc hcount m base with
    ⟨coreSteps, hbound, coreState, hcore⟩
  have hliteral := iterate_preservesLiteral (shiftSetupProgram false)
    (preservesLiteral_shiftSetupProgram false)
    (shiftSetupStartCfg state w accumulator count m base)
    (cleanReturnCfg (.controller .done) coreState
      (operandBoundaryBase w (cappedLeftValue w accumulator count w) m base))
    hcore
  have hover : operandLiteralOversized o
      (FullInterpreterState.moveLens.put coreState default) =
      operandLiteralOversized o state := by
    rw [operandLiteralOversized_move_put]
    exact operandLiteralOversized_eq_of_literal o coreState state hliteral
  rcases fullShift_finish o false returnLabel right state w accumulator count
      (cappedLeftValue w accumulator count w) m base coreSteps hbound coreState
      hcore with ⟨steps, hsteps, finalState, hrun⟩
  refine ⟨steps, hsteps, finalState, ?_⟩
  simpa [hover] using hrun

theorem fullShiftRight_correct {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N) (w accumulator count : Nat)
    (hw : 0 < w) (hacc : accumulator < 2 ^ w)
    (hcount : count < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    ∃ steps, steps <= fullShiftBound w ∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (fullShiftProgram o true returnLabel right)))^[steps])
        (some (mapLabelCfg Sum.inl
          (shiftSetupStartCfg state w accumulator count m base))) =
      some (mapLabelCfg Sum.inr
        (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                (if operandLiteralOversized o state
                  then 0 else cappedRightValue accumulator count w) m base))))) := by
  rcases shiftRightCore_correct state w accumulator count hw hacc hcount m base with
    ⟨coreSteps, hbound, coreState, hcore⟩
  have hliteral := iterate_preservesLiteral (shiftSetupProgram true)
    (preservesLiteral_shiftSetupProgram true)
    (shiftSetupStartCfg state w accumulator count m base)
    (cleanReturnCfg (.controller .done) coreState
      (operandBoundaryBase w (cappedRightValue accumulator count w) m base))
    hcore
  have hover : operandLiteralOversized o
      (FullInterpreterState.moveLens.put coreState default) =
      operandLiteralOversized o state := by
    rw [operandLiteralOversized_move_put]
    exact operandLiteralOversized_eq_of_literal o coreState state hliteral
  rcases fullShift_finish o true returnLabel right state w accumulator count
      (cappedRightValue accumulator count w) m base coreSteps hbound coreState
      hcore with ⟨steps, hsteps, finalState, hrun⟩
  refine ⟨steps, hsteps, finalState, ?_⟩
  simpa [hover] using hrun

abbrev ShiftInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (FullShiftLabel R)

def shiftInstructionProgram {N : Nat} {R : Type} (o : Op)
    (rightShift : Bool) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ShiftInstructionLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ShiftInstructionLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl ShiftSetupLabel.initialize)
    (fullShiftProgram o rightShift returnLabel right)

def shiftInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + fullShiftBound w

theorem shiftLeftInstruction_finish {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator : Nat) (hacc : accumulator < 2 ^ w) (hw : 0 < w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state operandState : FullInterpreterState N)
    (operandSteps : Nat) (hoperandBound : operandSteps <= operandEvalBound w m)
    (hoperand :
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o false returnLabel right)))^[
          operandSteps])
        (some (operandEvalStartCfg
          (R := FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inl
          (shiftSetupStartCfg operandState w accumulator
            (operandWordValue w o m) m base))))
    (hsemantic :
      (if operandLiteralOversized o operandState then 0
        else accumulator * 2 ^ operandWordValue w o m % 2 ^ w) =
      accumulator * 2 ^ sparseValue w o m % 2 ^ w) :
    ∃ steps, steps <= shiftInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o false returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inr
          (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w
                  (accumulator * 2 ^ sparseValue w o m % 2 ^ w)
                  m base)))))) := by
  have hcount := operandWordValue_lt w o m
  rcases fullShiftLeft_correct o returnLabel right operandState w accumulator
      (operandWordValue w o m) hw hacc hcount m base with
    ⟨shiftSteps, hshiftBound, finalState, hshift⟩
  rw [cappedLeftValue_width w accumulator (operandWordValue w o m) hacc]
    at hshift
  have hshiftLift := transport_iterate_operand_right o
    (Sum.inl ShiftSetupLabel.initialize)
    (fullShiftProgram o false returnLabel right) hshift
  have hall := chain_iterations
    (fun x : Option (TM2.Cfg
      (fun _ : CoreStack => SparseSymbol) (ShiftInstructionLabel o R)
      (FullInterpreterState N)) =>
      x.bind (TM2.step (shiftInstructionProgram o false returnLabel right)))
    hoperand hshiftLift
  refine ⟨operandSteps + shiftSteps, ?_, finalState, ?_⟩
  · simp [shiftInstructionBound]
    omega
  · simpa [shiftInstructionProgram, hsemantic] using hall

theorem shiftLeftInstruction_correct {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator : Nat) (hw : 0 < w) (hacc : accumulator < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= shiftInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o false returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inr
          (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w
                  (accumulator * 2 ^ sparseValue w o m % 2 ^ w)
                  m base)))))) := by
  cases o with
  | mem address =>
      rcases operandEval_correct (.mem address) hN w accumulator m hm
          (Sum.inl ShiftSetupLabel.initialize)
          (fullShiftProgram (.mem address) false returnLabel right)
          state base with ⟨operandSteps, hbound, operandState, hoperand⟩
      apply shiftLeftInstruction_finish (.mem address) hN returnLabel right
        w accumulator hacc hw m base state operandState operandSteps hbound
      · simpa [shiftInstructionProgram, shiftSetupStartCfg] using hoperand
      · simp [operandLiteralOversized, operandWordValue,
          Nat.mod_eq_of_lt (sparseValue_mem_lt hm address)]
  | ind address =>
      rcases operandEval_correct (.ind address) hN w accumulator m hm
          (Sum.inl ShiftSetupLabel.initialize)
          (fullShiftProgram (.ind address) false returnLabel right)
          state base with ⟨operandSteps, hbound, operandState, hoperand⟩
      apply shiftLeftInstruction_finish (.ind address) hN returnLabel right
        w accumulator hacc hw m base state operandState operandSteps hbound
      · simpa [shiftInstructionProgram, shiftSetupStartCfg] using hoperand
      · simp [operandLiteralOversized, operandWordValue,
          Nat.mod_eq_of_lt (sparseValue_ind_lt hm address)]
  | lit n =>
      change n <= N at hN
      let operandState := FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w, by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
      have hoperand := literalOperand_correct n hN w accumulator m
        (Sum.inl ShiftSetupLabel.initialize)
        (fullShiftProgram (.lit n) false returnLabel right) state base
      have hbound : 2 * w + 3 <= operandEvalBound w m := by
        simp [operandEvalBound]
        omega
      apply shiftLeftInstruction_finish (.lit n) hN returnLabel right
        w accumulator hacc hw m base state operandState (2 * w + 3) hbound
      · simpa [shiftInstructionProgram, operandEvalStartCfg, operandArgument,
          embedOperandReturnCfg, shiftSetupStartCfg, operandState] using hoperand
      · by_cases hnlt : n < 2 ^ w
        · have hzero : n / 2 ^ w = 0 :=
            (literalWord_remaining_eq_zero_iff n w).2 hnlt
          have hover : operandLiteralOversized (.lit n) operandState = false := by
            simp only [operandLiteralOversized]
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w, by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hzero]
          simp [hover, operandWordValue, sparseValue, Op.value,
            Nat.mod_eq_of_lt hnlt]
        · have hquot : n / 2 ^ w ≠ 0 := by
            intro hz
            exact hnlt ((literalWord_remaining_eq_zero_iff n w).1 hz)
          have hover : operandLiteralOversized (.lit n) operandState = true := by
            simp only [operandLiteralOversized]
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w, by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hquot]
          have hwn : w <= n := le_trans Nat.lt_two_pow_self.le
            (Nat.le_of_not_gt hnlt)
          have hdvd : 2 ^ w ∣ 2 ^ n := Nat.pow_dvd_pow 2 hwn
          have hresult : accumulator * 2 ^ n % 2 ^ w = 0 :=
            Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdvd accumulator)
          simp [hover, sparseValue, Op.value, hresult]

theorem shiftRightInstruction_finish {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator : Nat) (hacc : accumulator < 2 ^ w) (hw : 0 < w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state operandState : FullInterpreterState N)
    (operandSteps : Nat) (hoperandBound : operandSteps <= operandEvalBound w m)
    (hoperand :
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o true returnLabel right)))^[
          operandSteps])
        (some (operandEvalStartCfg
          (R := FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inl
          (shiftSetupStartCfg operandState w accumulator
            (operandWordValue w o m) m base))))
    (hsemantic :
      (if operandLiteralOversized o operandState then 0
        else accumulator / 2 ^ operandWordValue w o m) =
      accumulator / 2 ^ sparseValue w o m % 2 ^ w) :
    ∃ steps, steps <= shiftInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o true returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inr
          (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w
                  (accumulator / 2 ^ sparseValue w o m % 2 ^ w)
                  m base)))))) := by
  have hcount := operandWordValue_lt w o m
  rcases fullShiftRight_correct o returnLabel right operandState w accumulator
      (operandWordValue w o m) hw hacc hcount m base with
    ⟨shiftSteps, hshiftBound, finalState, hshift⟩
  rw [cappedRightValue_width w accumulator (operandWordValue w o m) hacc]
    at hshift
  have hshiftLift := transport_iterate_operand_right o
    (Sum.inl ShiftSetupLabel.initialize)
    (fullShiftProgram o true returnLabel right) hshift
  have hall := chain_iterations
    (fun x : Option (TM2.Cfg
      (fun _ : CoreStack => SparseSymbol) (ShiftInstructionLabel o R)
      (FullInterpreterState N)) =>
      x.bind (TM2.step (shiftInstructionProgram o true returnLabel right)))
    hoperand hshiftLift
  refine ⟨operandSteps + shiftSteps, ?_, finalState, ?_⟩
  · simp [shiftInstructionBound]
    omega
  · simpa [shiftInstructionProgram, hsemantic] using hall

theorem shiftRightInstruction_correct {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator : Nat) (hw : 0 < w) (hacc : accumulator < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= shiftInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o true returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inr
          (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w
                  (accumulator / 2 ^ sparseValue w o m % 2 ^ w)
                  m base)))))) := by
  cases o with
  | mem address =>
      rcases operandEval_correct (.mem address) hN w accumulator m hm
          (Sum.inl ShiftSetupLabel.initialize)
          (fullShiftProgram (.mem address) true returnLabel right)
          state base with ⟨operandSteps, hbound, operandState, hoperand⟩
      apply shiftRightInstruction_finish (.mem address) hN returnLabel right
        w accumulator hacc hw m base state operandState operandSteps hbound
      · simpa [shiftInstructionProgram, shiftSetupStartCfg] using hoperand
      · have hv := sparseValue_mem_lt hm address
        simp [operandLiteralOversized, operandWordValue,
          Nat.mod_eq_of_lt hv,
          Nat.mod_eq_of_lt (lt_of_le_of_lt
            (Nat.div_le_self accumulator (2 ^ sparseValue w (.mem address) m))
            hacc)]
  | ind address =>
      rcases operandEval_correct (.ind address) hN w accumulator m hm
          (Sum.inl ShiftSetupLabel.initialize)
          (fullShiftProgram (.ind address) true returnLabel right)
          state base with ⟨operandSteps, hbound, operandState, hoperand⟩
      apply shiftRightInstruction_finish (.ind address) hN returnLabel right
        w accumulator hacc hw m base state operandState operandSteps hbound
      · simpa [shiftInstructionProgram, shiftSetupStartCfg] using hoperand
      · have hv := sparseValue_ind_lt hm address
        simp [operandLiteralOversized, operandWordValue,
          Nat.mod_eq_of_lt hv,
          Nat.mod_eq_of_lt (lt_of_le_of_lt
            (Nat.div_le_self accumulator (2 ^ sparseValue w (.ind address) m))
            hacc)]
  | lit n =>
      change n <= N at hN
      let operandState := FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w, by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
      have hoperand := literalOperand_correct n hN w accumulator m
        (Sum.inl ShiftSetupLabel.initialize)
        (fullShiftProgram (.lit n) true returnLabel right) state base
      have hbound : 2 * w + 3 <= operandEvalBound w m := by
        simp [operandEvalBound]
        omega
      apply shiftRightInstruction_finish (.lit n) hN returnLabel right
        w accumulator hacc hw m base state operandState (2 * w + 3) hbound
      · simpa [shiftInstructionProgram, operandEvalStartCfg, operandArgument,
          embedOperandReturnCfg, shiftSetupStartCfg, operandState] using hoperand
      · by_cases hnlt : n < 2 ^ w
        · have hzero : n / 2 ^ w = 0 :=
            (literalWord_remaining_eq_zero_iff n w).2 hnlt
          have hover : operandLiteralOversized (.lit n) operandState = false := by
            simp only [operandLiteralOversized]
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w, by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hzero]
          have hdivlt : accumulator / 2 ^ n < 2 ^ w :=
            lt_of_le_of_lt (Nat.div_le_self _ _) hacc
          simp [hover, operandWordValue, sparseValue, Op.value,
            Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hdivlt]
        · have hquot : n / 2 ^ w ≠ 0 := by
            intro hz
            exact hnlt ((literalWord_remaining_eq_zero_iff n w).1 hz)
          have hover : operandLiteralOversized (.lit n) operandState = true := by
            simp only [operandLiteralOversized]
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w, by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hquot]
          have hpow : 2 ^ w <= 2 ^ n := Nat.pow_le_pow_right (by omega)
            (le_trans Nat.lt_two_pow_self.le (Nat.le_of_not_gt hnlt))
          have hzeroResult : accumulator / 2 ^ n = 0 :=
            Nat.div_eq_of_lt (lt_of_lt_of_le hacc hpow)
          simp [hover, sparseValue, Op.value, hzeroResult]

end Lax51Proofs.RamToTM
