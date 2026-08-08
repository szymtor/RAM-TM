import Lax20Proofs.RamToTM.CyclicEmbedding
import Lax20Proofs.RamToTM.CountdownGlobal
import Lax20Proofs.RamToTM.ShiftLeftRound
import Lax20Proofs.RamToTM.ShiftRightRound

namespace Lax20Proofs.RamToTM

open Turing TM2

inductive CappedShiftLabel
  | countdown (label : CountdownLabel)
  | fuel
  | left (label : ShiftLeftRoundLabel Unit)
  | right (label : ShiftRightRoundLabel Unit)
  | cleanupFuel
  | cleanupCount
  | cleanupTemp
  | done
  deriving DecidableEq, Fintype, Inhabited

def resetShiftControls {N : Nat} (state : FullInterpreterState N) :
    FullInterpreterState N :=
  FullInterpreterState.shiftLens.put
    (FullInterpreterState.countdownLens.put
      (FullInterpreterState.moveLens.put state default) default) default

@[simp] theorem resetShiftControls_move {N : Nat}
    (state : FullInterpreterState N) :
    FullInterpreterState.moveLens.get (resetShiftControls state) = default := by
  cases state <;> rfl

@[simp] theorem resetShiftControls_countdown {N : Nat}
    (state : FullInterpreterState N) :
    FullInterpreterState.countdownLens.get (resetShiftControls state) = default := by
  cases state <;> rfl

@[simp] theorem resetShiftControls_shift {N : Nat}
    (state : FullInterpreterState N) :
    FullInterpreterState.shiftLens.get (resetShiftControls state) = default := by
  cases state <;> rfl

def embedCountdownController : Sum CountdownLabel CappedShiftLabel ->
    CappedShiftLabel
  | .inl label => .countdown label
  | .inr label => label

def cappedShiftCleanupStmt {N : Nat} (stack : CoreStack)
    (again next : CappedShiftLabel) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N) :=
  .pop stack
    (fun s a => FullInterpreterState.moveLens.put s ⟨a⟩) <|
  .branch (fun s =>
      (FullInterpreterState.moveLens.get s).held.isNone)
    (.goto fun _ => next)
    (.load (fun s => FullInterpreterState.moveLens.put s default) <|
      .goto fun _ => again)

def cappedShiftProgram {N : Nat} (rightShift : Bool) :
    CappedShiftLabel -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)
  | .countdown label =>
      mapLabelStmt embedCountdownController <|
        countdownMultiLeft .cleanupFuel .fuel label
  | .fuel =>
      .pop .work1
        (fun s a => FullInterpreterState.moveLens.put s ⟨a⟩) <|
      .branch (fun s =>
          (FullInterpreterState.moveLens.get s).held.isNone)
        (.goto fun _ => .cleanupFuel)
        (.load resetShiftControls <|
          .goto fun _ => if rightShift
            then .right (Sum.inl ShiftRightLabel.discard)
            else .left (Sum.inl ShiftLabel.first))
  | .left (Sum.inr (Sum.inr (Sum.inr ()))) =>
      .load (fun s => FullInterpreterState.countdownLens.put s default) <|
        .goto fun _ => .countdown .scan
  | .left label =>
      mapLabelStmt CappedShiftLabel.left <|
        shiftLeftRoundProgram () (fun _ => .halt) label
  | .right (Sum.inr (Sum.inr (Sum.inr ()))) =>
      .load (fun s => FullInterpreterState.countdownLens.put s default) <|
        .goto fun _ => .countdown .scan
  | .right label =>
      mapLabelStmt CappedShiftLabel.right <|
        shiftRightRoundProgram () (fun _ => .halt) label
  | .cleanupFuel =>
      cappedShiftCleanupStmt .work1 .cleanupFuel .cleanupCount
  | .cleanupCount =>
      cappedShiftCleanupStmt .work3 .cleanupCount .cleanupTemp
  | .cleanupTemp =>
      cappedShiftCleanupStmt .work4 .cleanupTemp .done
  | .done => .halt

def cappedShiftStacks (w word count : Nat)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol :=
  shiftRoundBase w word count fuel m base

def cappedShiftCfg {N : Nat} (label : CappedShiftLabel)
    (state : FullInterpreterState N) (w word count : Nat)
    (fuel : List SparseSymbol) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N) :=
  cleanReturnCfg label state (cappedShiftStacks w word count fuel m base)

end Lax20Proofs.RamToTM
