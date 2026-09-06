import Lax51Proofs.RamToTM.FullDivideMacro

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

def operandLiteralOversized {N : Nat} (o : Op)
    (state : FullInterpreterState N) : Bool :=
  match o with
  | .lit _ => (FullInterpreterState.literalLens.get state).remaining.val != 0
  | .mem _ | .ind _ => false

inductive ConditionalZeroLabel
  | rewrite | done
  deriving DecidableEq, Fintype, Inhabited

def conditionalZeroProgram (N : Nat) (o : Op) : ConditionalZeroLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) ConditionalZeroLabel
      (FullInterpreterState N)
  | .rewrite =>
      .pop .accumulator
        (fun s a => FullInterpreterState.moveLens.put s ⟨a⟩) <|
      .branch (fun s => (FullInterpreterState.moveLens.get s).held.isNone)
        (.load (fun s => FullInterpreterState.moveLens.put s default) <|
          .goto fun _ => .done)
        (.push .work0 (fun s =>
            if operandLiteralOversized o s then .bit false
            else (FullInterpreterState.moveLens.get s).held.getD (.bit false)) <|
          .load (fun s => FullInterpreterState.moveLens.put s default) <|
            .goto fun _ => .rewrite)
  | .done => .halt

def conditionalZeroCfg {N : Nat} (label : ConditionalZeroLabel)
    (state : FullInterpreterState N) (source target : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) ConditionalZeroLabel
      (FullInterpreterState N) where
  l := some label
  var := state
  stk := fun
    | .accumulator => source
    | .work0 => target
    | k => base k

@[simp] theorem operandLiteralOversized_move_put {N : Nat} (o : Op)
    (state : FullInterpreterState N) (move : SymbolMoveControl) :
    operandLiteralOversized o (FullInterpreterState.moveLens.put state move) =
      operandLiteralOversized o state := by
  cases o <;> rfl

@[simp] theorem conditionalZero_step_nil {N : Nat} (o : Op)
    (state : FullInterpreterState N) (target : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol) :
    TM2.step (conditionalZeroProgram N o)
      (conditionalZeroCfg .rewrite state [] target base) =
    some (conditionalZeroCfg .done
      (FullInterpreterState.moveLens.put state default) [] target base) := by
  simp [conditionalZeroProgram, conditionalZeroCfg, TM2.step,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]

@[simp] theorem conditionalZero_step_cons {N : Nat} (o : Op)
    (state : FullInterpreterState N) (x : SparseSymbol)
    (xs target : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol) :
    TM2.step (conditionalZeroProgram N o)
      (conditionalZeroCfg .rewrite state (x :: xs) target base) =
    some (conditionalZeroCfg .rewrite
      (FullInterpreterState.moveLens.put state default) xs
      ((if operandLiteralOversized o state then .bit false else x) :: target)
      base) := by
  simp [conditionalZeroProgram, conditionalZeroCfg, TM2.step,
    Function.update, FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> rfl

def conditionallyRewritten (zero : Bool) (source : List SparseSymbol) :
    List SparseSymbol :=
  if zero then List.replicate source.length (.bit false) else source.reverse

theorem conditionalZero_iterate {N : Nat} (o : Op)
    (state : FullInterpreterState N) (source target : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    ((fun x => x.bind (TM2.step (conditionalZeroProgram N o)))^[source.length])
      (some (conditionalZeroCfg .rewrite state source target base)) =
    some (conditionalZeroCfg .rewrite
      (FullInterpreterState.moveLens.put state default) []
      (conditionallyRewritten (operandLiteralOversized o state) source ++ target)
      base) := by
  induction source generalizing state target base with
  | nil =>
      have hs : FullInterpreterState.moveLens.put state default = state := by
        rw [← hmove, FullInterpreterState.moveLens.put_get]
      simp [conditionallyRewritten, hs]
  | cons x xs ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, conditionalZero_step_cons]
      rw [ih (FullInterpreterState.moveLens.put state default)
        ((if operandLiteralOversized o state then .bit false else x) :: target)
        base (FullInterpreterState.moveLens.get_put _ _)]
      by_cases h : operandLiteralOversized o state <;>
        simp [conditionallyRewritten, h, List.replicate_succ,
          List.reverse_cons, List.append_assoc,
          FullInterpreterState.moveLens.put_put,
          replicate_append_same_cons]

theorem conditionalZero_correct {N : Nat} (o : Op)
    (state : FullInterpreterState N) (source : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    ((fun x => x.bind (TM2.step (conditionalZeroProgram N o)))^[source.length + 1])
      (some (conditionalZeroCfg .rewrite state source [] base)) =
    some (conditionalZeroCfg .done
      (FullInterpreterState.moveLens.put state default) []
      (conditionallyRewritten (operandLiteralOversized o state) source) base) := by
  rw [Nat.add_comm, Function.iterate_add_apply,
    conditionalZero_iterate o state source [] base hmove]
  simp only [List.append_nil, Function.iterate_one, Option.bind_some,
    conditionalZero_step_nil, FullInterpreterState.moveLens.put_put]

end Lax51Proofs.RamToTM
