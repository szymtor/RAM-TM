import Lax20Proofs.RamToTM.FullSubtractCore

namespace Lax20Proofs.RamToTM

open Turing TM2

inductive ConditionalInstallLabel
  | loop | done
  deriving DecidableEq, Fintype, Inhabited

def subtractInstallZero {N : Nat} (state : FullInterpreterState N) : Bool :=
  (FullInterpreterState.subLens.get state).borrow || state.subtractForceZero

def conditionalInstallProgram (N : Nat) : ConditionalInstallLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) ConditionalInstallLabel
      (FullInterpreterState N)
  | .loop =>
      .pop .work0
        (fun s a => FullInterpreterState.moveLens.put s ⟨a⟩) <|
      .branch (fun s => (FullInterpreterState.moveLens.get s).held.isNone)
        (.load (fun s => FullInterpreterState.moveLens.put s default) <|
          .goto fun _ => .done)
        (.push .accumulator (fun s =>
            if subtractInstallZero s then .bit false
            else (FullInterpreterState.moveLens.get s).held.getD (.bit false)) <|
          .load (fun s => FullInterpreterState.moveLens.put s default) <|
            .goto fun _ => .loop)
  | .done => .halt

def conditionalInstallCfg {N : Nat} (label : ConditionalInstallLabel)
    (state : FullInterpreterState N) (source accumulator : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) ConditionalInstallLabel
      (FullInterpreterState N) where
  l := some label
  var := state
  stk := fun
    | .work0 => source
    | .accumulator => accumulator
    | k => base k

@[simp] theorem subLens_get_moveLens_put {N : Nat}
    (state : FullInterpreterState N) (move : SymbolMoveControl) :
    FullInterpreterState.subLens.get
      (FullInterpreterState.moveLens.put state move) =
    FullInterpreterState.subLens.get state := by
  rfl

@[simp] theorem subtractInstallZero_moveLens_put {N : Nat}
    (state : FullInterpreterState N) (move : SymbolMoveControl) :
    subtractInstallZero (FullInterpreterState.moveLens.put state move) =
      subtractInstallZero state := by
  rfl

@[simp] theorem conditionalInstall_step_nil {N : Nat}
    (state : FullInterpreterState N) (accumulator : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol) :
    TM2.step (conditionalInstallProgram N)
      (conditionalInstallCfg .loop state [] accumulator base) =
    some (conditionalInstallCfg .done
      (FullInterpreterState.moveLens.put state default) [] accumulator
      base) := by
  simp [conditionalInstallProgram, conditionalInstallCfg, TM2.step]
  simp [FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]

@[simp] theorem conditionalInstall_step_cons {N : Nat}
    (state : FullInterpreterState N) (x : SparseSymbol)
    (xs accumulator : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol) :
    TM2.step (conditionalInstallProgram N)
      (conditionalInstallCfg .loop state (x :: xs) accumulator base) =
    some (conditionalInstallCfg .loop
      (FullInterpreterState.moveLens.put state default) xs
      ((if subtractInstallZero state then .bit false else x) ::
        accumulator) base) := by
  simp [conditionalInstallProgram, conditionalInstallCfg, TM2.step,
    Function.update, FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> rfl

def conditionalInstalled (borrow : Bool) (source : List SparseSymbol) :
    List SparseSymbol :=
  if borrow then List.replicate source.length (.bit false) else source.reverse

theorem conditionalInstall_iterate {N : Nat}
    (state : FullInterpreterState N) (source accumulator : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    ((fun o => o.bind (TM2.step (conditionalInstallProgram N)))^[source.length])
      (some (conditionalInstallCfg .loop state source accumulator base)) =
    some (conditionalInstallCfg .loop
      (FullInterpreterState.moveLens.put state default) []
      (conditionalInstalled (subtractInstallZero state) source ++
        accumulator) base) := by
  induction source generalizing state accumulator base with
  | nil =>
      have hstate : FullInterpreterState.moveLens.put state default = state := by
        rw [← hmove, FullInterpreterState.moveLens.put_get]
      simp [conditionalInstalled, hstate]
  | cons x xs ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, conditionalInstall_step_cons]
      rw [ih (FullInterpreterState.moveLens.put state default)
        ((if subtractInstallZero state then .bit false else x) ::
          accumulator) base (FullInterpreterState.moveLens.get_put _ _)]
      simp [conditionalInstalled, List.replicate_succ, List.reverse_cons,
        List.append_assoc]
      by_cases h : subtractInstallZero state <;>
        simp [h, subLens_get_moveLens_put, List.append_assoc,
          FullInterpreterState.moveLens.put_put,
          replicate_append_same_cons]

theorem conditionalInstall_correct {N : Nat}
    (state : FullInterpreterState N) (source : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    ((fun o => o.bind (TM2.step (conditionalInstallProgram N)))^[source.length + 1])
      (some (conditionalInstallCfg .loop state source [] base)) =
    some (conditionalInstallCfg .done
      (FullInterpreterState.moveLens.put state default) []
      (conditionalInstalled (subtractInstallZero state) source)
      base) := by
  rw [Nat.add_comm, Function.iterate_add_apply,
    conditionalInstall_iterate state source [] base hmove]
  simp only [List.append_nil, Function.iterate_one, Option.bind_some,
    conditionalInstall_step_nil, FullInterpreterState.moveLens.put_put]

end Lax20Proofs.RamToTM
