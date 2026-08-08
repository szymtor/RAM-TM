import Lax20Proofs.RamToTM.FullInterpreterState

namespace Lax20Proofs.RamToTM

open Turing TM2

/-! A small but important cleanup macro.  Unlike `SymbolMoveMacro`, this
macro consumes a work stack without leaving its contents on another tape.
This gives the compound interpreter honest clean phase boundaries. -/

inductive DiscardStack
  | data
  deriving DecidableEq, Fintype, Inhabited

inductive DiscardLabel
  | loop | done
  deriving DecidableEq, Fintype, Inhabited

def discardProgram : DiscardLabel →
    TM2.Stmt (fun _ : DiscardStack => SparseSymbol)
      DiscardLabel SymbolMoveControl
  | .loop =>
      .pop .data (fun _ a => ⟨a⟩) <|
        .branch (fun s => s.held.isNone)
          (.load (fun _ => default) <| .goto fun _ => .done)
          (.load (fun _ => default) <| .goto fun _ => .loop)
  | .done => .halt

def discardStacks (data : List SparseSymbol) :
    DiscardStack → List SparseSymbol
  | .data => data

def discardCfg (label : DiscardLabel) (data : List SparseSymbol) :
    TM2.Cfg (fun _ : DiscardStack => SparseSymbol)
      DiscardLabel SymbolMoveControl where
  l := some label
  var := default
  stk := discardStacks data

def discardCfgState (label : DiscardLabel) (state : SymbolMoveControl)
    (data : List SparseSymbol) :
    TM2.Cfg (fun _ : DiscardStack => SparseSymbol)
      DiscardLabel SymbolMoveControl where
  l := some label
  var := state
  stk := discardStacks data

theorem discardCfgState_default (label : DiscardLabel)
    (data : List SparseSymbol) :
    discardCfgState label default data = discardCfg label data := rfl

@[simp] theorem discard_step_state_nil (state : SymbolMoveControl) :
    TM2.step discardProgram (discardCfgState .loop state []) =
      some (discardCfg .done []) := by
  simp [TM2.step, discardProgram, discardCfgState, discardCfg, discardStacks]

@[simp] theorem discard_step_state_cons (state : SymbolMoveControl)
    (a : SparseSymbol) (data : List SparseSymbol) :
    TM2.step discardProgram (discardCfgState .loop state (a :: data)) =
      some (discardCfg .loop data) := by
  simp [TM2.step, discardProgram, discardCfgState, discardCfg, discardStacks]
  congr 2
  funext k
  cases k
  rfl

@[simp] theorem discard_step_nil :
    TM2.step discardProgram (discardCfg .loop []) =
      some (discardCfg .done []) := by
  simp [TM2.step, discardProgram, discardCfg, discardStacks]

@[simp] theorem discard_step_cons (a : SparseSymbol)
    (data : List SparseSymbol) :
    TM2.step discardProgram (discardCfg .loop (a :: data)) =
      some (discardCfg .loop data) := by
  simp [TM2.step, discardProgram, discardCfg, discardStacks]
  congr 2
  funext k
  cases k
  rfl

theorem discard_iterate (data : List SparseSymbol) :
    ((fun o : Option (TM2.Cfg (fun _ : DiscardStack => SparseSymbol)
        DiscardLabel SymbolMoveControl) => o.bind (TM2.step discardProgram))^[data.length])
      (some (discardCfg .loop data)) =
        some (discardCfg .loop []) := by
  induction data with
  | nil => rfl
  | cons a data ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, discard_step_cons]
      exact ih

theorem discard_correct (data : List SparseSymbol) :
    ((fun o : Option (TM2.Cfg (fun _ : DiscardStack => SparseSymbol)
        DiscardLabel SymbolMoveControl) => o.bind (TM2.step discardProgram))^[data.length + 1])
      (some (discardCfg .loop data)) =
        some (discardCfg .done []) := by
  rw [Nat.add_comm, Function.iterate_add_apply, discard_iterate]
  simp only [Function.iterate_one, Option.bind_some, discard_step_nil]

theorem discard_correct_from (state : SymbolMoveControl)
    (data : List SparseSymbol) :
    ((fun o : Option (TM2.Cfg (fun _ : DiscardStack => SparseSymbol)
        DiscardLabel SymbolMoveControl) => o.bind (TM2.step discardProgram))^[data.length + 1])
      (some (discardCfgState .loop state data)) =
        some (discardCfg .done []) := by
  cases data with
  | nil => simpa using discard_step_state_nil state
  | cons a data =>
      rw [List.length_cons, show data.length + 1 + 1 = (data.length + 1) + 1 by omega,
        Function.iterate_succ_apply]
      simp only [Option.bind_some, discard_step_state_cons]
      exact discard_correct data

def discardCoreRenaming (target : CoreStack) :
    StackRenaming DiscardStack CoreStack where
  encode := fun _ => target
  decode := fun k => if k = target then some .data else none
  decode_encode := by intro k; cases k; simp
  encode_decode := by
    intro k' k h
    cases k
    by_cases hk : k' = target
    · exact hk.symm
    · simp [hk] at h

theorem discard_core_correct {N : ℕ} {R : Type}
    (target : CoreStack) (data : List SparseSymbol) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum DiscardLabel R) (FullInterpreterState N))
    (ambientState : FullInterpreterState N)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram
      (discardCoreRenaming target) FullInterpreterState.moveLens
      discardProgram .done returnLabel right)))^[data.length + 2])
      (some (lensRenamedCfg (discardCoreRenaming target)
        FullInterpreterState.moveLens (discardCfg .loop data)
        ambientState ambientStacks)) =
      some (lensReturnCfg (discardCoreRenaming target)
        FullInterpreterState.moveLens returnLabel (discardCfg .done [])
        ambientState ambientStacks) := by
  convert transport_lensHaltingMacro_and_return
    (discardCoreRenaming target) FullInterpreterState.moveLens
    discardProgram .done (by rfl) returnLabel right
    (discard_correct data) rfl ambientState ambientStacks using 1 <;> omega

end Lax20Proofs.RamToTM
