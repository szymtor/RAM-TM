import Lax51Proofs.RamToTM.CappedShiftController

namespace Lax51Proofs.RamToTM

open Turing TM2

def PreservesLiteral {N : Nat} {Λ : Type}
    (stmt : TM2.Stmt (fun _ : CoreStack => SparseSymbol) Λ
      (FullInterpreterState N)) : Prop :=
  ∀ state tapes,
    (TM2.stepAux stmt state tapes).var.literal = state.literal

def ProgramPreservesLiteral {N : Nat} {Λ : Type}
    (program : Λ -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) Λ
      (FullInterpreterState N)) : Prop :=
  ∀ label, PreservesLiteral (program label)

theorem step_preservesLiteral {N : Nat} {Λ : Type}
    (program : Λ -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) Λ
      (FullInterpreterState N))
    (hprogram : ProgramPreservesLiteral program)
    (c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) Λ
      (FullInterpreterState N))
    (hstep : TM2.step program c = some d) :
    d.var.literal = c.var.literal := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => contradiction
  | some label =>
      simp only [TM2.step] at hstep
      have hd := Option.some.inj hstep
      subst d
      exact hprogram label state tapes

theorem iterate_preservesLiteral {N : Nat} {Λ : Type}
    (program : Λ -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) Λ
      (FullInterpreterState N))
    (hprogram : ProgramPreservesLiteral program)
    {n : Nat}
    (c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) Λ
      (FullInterpreterState N))
    (hrun : ((fun x => x.bind (TM2.step program))^[n]) (some c) = some d) :
    d.var.literal = c.var.literal := by
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hrun
      subst d
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun
      simp only [Option.bind_some] at hrun
      cases hs : TM2.step program c with
      | none =>
          rw [hs, iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          rw [hs] at hrun
          exact (ih c' hrun).trans (step_preservesLiteral program hprogram c c' hs)

theorem preservesLiteral_mapLabel {N : Nat} {Λ Λ' : Type}
    (encode : Λ -> Λ')
    (stmt : TM2.Stmt (fun _ : CoreStack => SparseSymbol) Λ
      (FullInterpreterState N))
    (h : PreservesLiteral stmt) :
    PreservesLiteral (mapLabelStmt encode stmt) := by
  intro state tapes
  rw [stepAux_mapLabelStmt]
  exact h state tapes

theorem preservesLiteral_lensRename {N : Nat}
    {K Λ R σ : Type} [DecidableEq K]
    (stackMap : StackRenaming K CoreStack)
    (lens : StateLens σ (FullInterpreterState N))
    (hput : ∀ state value, (lens.put state value).literal = state.literal)
    (stmt : TM2.Stmt (fun _ : K => SparseSymbol) Λ σ) :
    PreservesLiteral
      (lensRenameStmt (Λx := R) stackMap lens stmt) := by
  induction stmt with
  | push k f stmt ih =>
      intro state tapes
      simp only [lensRenameStmt, TM2.stepAux]
      exact ih _ _
  | peek k f stmt ih =>
      intro state tapes
      simp only [lensRenameStmt, TM2.stepAux]
      rw [ih, hput]
  | pop k f stmt ih =>
      intro state tapes
      simp only [lensRenameStmt, TM2.stepAux]
      rw [ih, hput]
  | load f stmt ih =>
      intro state tapes
      simp only [lensRenameStmt, TM2.stepAux]
      rw [ih, hput]
  | branch f left right ihLeft ihRight =>
      intro state tapes
      simp only [lensRenameStmt, TM2.stepAux]
      by_cases h : f (lens.get state)
      · simp only [h]
        exact ihLeft state tapes
      · simp only [h]
        exact ihRight state tapes
  | goto f => intro state tapes; rfl
  | halt => intro state tapes; rfl

theorem preservesLiteral_lensPhase {N : Nat}
    {K Λ R σ : Type} [DecidableEq K] [DecidableEq Λ]
    (stackMap : StackRenaming K CoreStack)
    (lens : StateLens σ (FullInterpreterState N))
    (hput : ∀ state value, (lens.put state value).literal = state.literal)
    (program : Λ -> TM2.Stmt (fun _ : K => SparseSymbol) Λ σ)
    (done : Λ) (entry : R) (label : Λ) :
    PreservesLiteral
      (lensPhaseLeft stackMap lens program done entry label) := by
  simp only [lensPhaseLeft]
  split
  · intro state tapes; rfl
  · exact preservesLiteral_lensRename stackMap lens hput (program label)

@[simp] theorem literal_move_put {N : Nat} (state : FullInterpreterState N)
    (value : SymbolMoveControl) :
    (FullInterpreterState.moveLens.put state value).literal = state.literal := by
  cases state <;> rfl

@[simp] theorem literal_shift_put {N : Nat} (state : FullInterpreterState N)
    (value : MoveControl) :
    (FullInterpreterState.shiftLens.put state value).literal = state.literal := by
  cases state <;> rfl

@[simp] theorem literal_countdown_put {N : Nat}
    (state : FullInterpreterState N) (value : CountdownControl) :
    (FullInterpreterState.countdownLens.put state value).literal =
      state.literal := by
  cases state <;> rfl

@[simp] theorem literal_resetShiftControls {N : Nat}
    (state : FullInterpreterState N) :
    (resetShiftControls state).literal = state.literal := by
  cases state <;> rfl

theorem preservesLiteral_shiftLeftRound {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (hright : ∀ label, PreservesLiteral (right label))
    (label : ShiftLeftRoundLabel R) :
    PreservesLiteral (shiftLeftRoundProgram returnLabel right label) := by
  rcases label with label | tail
  · exact preservesLiteral_lensPhase shiftRoundRenaming
      FullInterpreterState.shiftLens literal_shift_put
      sparseShiftLeftCoreProgram .done (Sum.inl SymbolMoveLabel.loop) label
  rcases tail with label | tail
  · apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_lensPhase
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens literal_move_put symbolMoveCoreProgram
      .done (Sum.inl SymbolMoveLabel.loop) label
  rcases tail with label | label
  · apply preservesLiteral_mapLabel Sum.inr
    apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_lensPhase
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens literal_move_put symbolMoveCoreProgram
      .done returnLabel label
  · apply preservesLiteral_mapLabel Sum.inr
    apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_mapLabel Sum.inr (right label) (hright label)

theorem preservesLiteral_shiftRightRound {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (hright : ∀ label, PreservesLiteral (right label))
    (label : ShiftRightRoundLabel R) :
    PreservesLiteral (shiftRightRoundProgram returnLabel right label) := by
  rcases label with label | tail
  · exact preservesLiteral_lensPhase shiftRoundRenaming
      FullInterpreterState.shiftLens literal_shift_put
      sparseShiftRightCoreProgram .done (Sum.inl SymbolMoveLabel.loop) label
  rcases tail with label | tail
  · apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_lensPhase
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens literal_move_put symbolMoveCoreProgram
      .done (Sum.inl SymbolMoveLabel.loop) label
  rcases tail with label | label
  · apply preservesLiteral_mapLabel Sum.inr
    apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_lensPhase
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens literal_move_put symbolMoveCoreProgram
      .done returnLabel label
  · apply preservesLiteral_mapLabel Sum.inr
    apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_mapLabel Sum.inr (right label) (hright label)

theorem preservesLiteral_countdownMultiLeft {N : Nat} {R : Type}
    (zeroLabel positiveLabel : R) (label : CountdownLabel) :
    PreservesLiteral
      (countdownMultiLeft (N := N) zeroLabel positiveLabel label) := by
  simp only [countdownMultiLeft, lensMultiPhaseLeft]
  split
  · intro state tapes
    simp [TM2.stepAux, countdownOnExit]
  · exact preservesLiteral_lensRename countdownCoreRenaming
      FullInterpreterState.countdownLens literal_countdown_put
      (sparseCountdownProgram label)

theorem preservesLiteral_cleanupStmt {N : Nat}
    (stack : CoreStack) (again next : CappedShiftLabel) :
    PreservesLiteral (N := N)
      (cappedShiftCleanupStmt stack again next) := by
  intro state tapes
  simp [cappedShiftCleanupStmt, TM2.stepAux,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  cases h : (tapes stack).head? <;>
    simp [h, literal_move_put]

theorem preservesLiteral_cappedShiftProgram {N : Nat}
    (rightShift : Bool) (label : CappedShiftLabel) :
    PreservesLiteral (cappedShiftProgram (N := N) rightShift label) := by
  cases label with
  | countdown label =>
      exact preservesLiteral_mapLabel embedCountdownController
        (countdownMultiLeft CappedShiftLabel.cleanupFuel CappedShiftLabel.fuel label)
        (preservesLiteral_countdownMultiLeft CappedShiftLabel.cleanupFuel
          CappedShiftLabel.fuel label)
  | fuel =>
      intro state tapes
      simp [cappedShiftProgram, TM2.stepAux,
        FullInterpreterState.moveLens.get_put,
        FullInterpreterState.moveLens.put_put, literal_resetShiftControls]
      cases h : (tapes CoreStack.work1).head? <;>
        simp [h, literal_move_put, literal_resetShiftControls]
  | left label =>
      rcases label with label | tail
      · exact preservesLiteral_mapLabel CappedShiftLabel.left
          (shiftLeftRoundProgram () (fun _ => .halt) (Sum.inl label))
          (preservesLiteral_shiftLeftRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl) (Sum.inl label))
      rcases tail with label | tail
      · exact preservesLiteral_mapLabel CappedShiftLabel.left
          (shiftLeftRoundProgram () (fun _ => .halt)
            (Sum.inr (Sum.inl label)))
          (preservesLiteral_shiftLeftRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl) (Sum.inr (Sum.inl label)))
      rcases tail with label | terminal
      · exact preservesLiteral_mapLabel CappedShiftLabel.left
          (shiftLeftRoundProgram () (fun _ => .halt)
            (Sum.inr (Sum.inr (Sum.inl label))))
          (preservesLiteral_shiftLeftRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl)
            (Sum.inr (Sum.inr (Sum.inl label))))
      · cases terminal
        intro state tapes
        simp [cappedShiftProgram, TM2.stepAux]
  | right label =>
      rcases label with label | tail
      · exact preservesLiteral_mapLabel CappedShiftLabel.right
          (shiftRightRoundProgram () (fun _ => .halt) (Sum.inl label))
          (preservesLiteral_shiftRightRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl) (Sum.inl label))
      rcases tail with label | tail
      · exact preservesLiteral_mapLabel CappedShiftLabel.right
          (shiftRightRoundProgram () (fun _ => .halt)
            (Sum.inr (Sum.inl label)))
          (preservesLiteral_shiftRightRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl) (Sum.inr (Sum.inl label)))
      rcases tail with label | terminal
      · exact preservesLiteral_mapLabel CappedShiftLabel.right
          (shiftRightRoundProgram () (fun _ => .halt)
            (Sum.inr (Sum.inr (Sum.inl label))))
          (preservesLiteral_shiftRightRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl)
            (Sum.inr (Sum.inr (Sum.inl label))))
      · cases terminal
        intro state tapes
        simp [cappedShiftProgram, TM2.stepAux]
  | cleanupFuel =>
      exact preservesLiteral_cleanupStmt .work1 .cleanupFuel .cleanupCount
  | cleanupCount =>
      exact preservesLiteral_cleanupStmt .work3 .cleanupCount .cleanupTemp
  | cleanupTemp =>
      exact preservesLiteral_cleanupStmt .work4 .cleanupTemp .done
  | done => intro state tapes; rfl

end Lax51Proofs.RamToTM
