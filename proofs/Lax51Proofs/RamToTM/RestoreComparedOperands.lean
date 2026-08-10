import Lax51Proofs.RamToTM.CompareCoreMacro

namespace Lax51Proofs.RamToTM

open Turing TM2

set_option maxHeartbeats 800000

private theorem restore_iterate_two_more {X : Type} (f : X -> X) (n : Nat)
    {x y : X} (h : (f^[n]) (f (f x)) = y) :
    (f^[n + 2]) x = y := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    Function.iterate_succ_apply, Function.iterate_succ_apply]
  exact h

abbrev RestoreComparedTailLabel (R : Type) := Sum SymbolMoveLabel R
abbrev RestoreComparedLabel (R : Type) :=
  Sum SymbolMoveLabel (RestoreComparedTailLabel R)

def restoreComparedTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    RestoreComparedTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (RestoreComparedTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work3 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def restoreComparedProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    RestoreComparedLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (RestoreComparedLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work2 .accumulator (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (restoreComparedTailProgram returnLabel right)

def restoredCompareStacks (w a b : Nat)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w a).map SparseSymbol.bit
  | .work1 => (fixedBits w b).map SparseSymbol.bit
  | .work2 | .work3 => []
  | k => base k

theorem restoreFirst_bridge {N : Nat} {R : Type}
    (w a b : Nat) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work2 .accumulator (by decide))
      FullInterpreterState.moveLens
      (Sum.inl SymbolMoveLabel.loop : RestoreComparedTailLabel R)
      (symbolMoveLocalCfg .done []
        ((fixedBits w a).map SparseSymbol.bit))
      state (compareResultStacks w a b base) =
    lensRenamedCfg (Λx := R)
      (symbolMoveCoreRenaming .work3 .work1 (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((fixedBits w b).reverse.map SparseSymbol.bit) [])
      (FullInterpreterState.moveLens.put state default)
      (fun
        | .accumulator => (fixedBits w a).map SparseSymbol.bit
        | .work2 => []
        | .work3 => (fixedBits w b).reverse.map SparseSymbol.bit
        | k => compareResultStacks w a b base k) := by
  simp [phaseReturnCfg, lensRenamedCfg, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
    compareResultStacks, renamedStacks]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
      symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
      compareResultStacks, List.map_reverse]

theorem restoreSecond_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w a b : Nat)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work3 .work1 (by decide))
      FullInterpreterState.moveLens returnLabel
      (symbolMoveLocalCfg .done [] ((fixedBits w b).map SparseSymbol.bit))
      state
      (fun
        | .accumulator => (fixedBits w a).map SparseSymbol.bit
        | .work2 => []
        | .work3 => (fixedBits w b).reverse.map SparseSymbol.bit
        | k => compareResultStacks w a b base k) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (restoredCompareStacks w a b base) := by
  simp [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, compareResultStacks, restoredCompareStacks,
    renamedStacks]
  funext k
  cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
    compareResultStacks, restoredCompareStacks, List.map_reverse]

theorem restoreCompared_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b : Nat) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ finalState,
      ((fun o => o.bind (TM2.step
        (restoreComparedProgram returnLabel right)))^[2 * w + 4])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work2 .accumulator (by decide))
          FullInterpreterState.moveLens
          (symbolMoveLocalCfg .loop
            ((fixedBits w a).reverse.map SparseSymbol.bit) [])
          state (compareResultStacks w a b base))) =
      some (mapLabelCfg (fun l : RestoreComparedTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l : R => Sum.inr l)
          (cleanReturnCfg returnLabel finalState
            (restoredCompareStacks w a b base)))) := by
  have hfirst := run_lensPhase_to_right
    (symbolMoveCoreRenaming .work2 .accumulator (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop)
    (restoreComparedTailProgram returnLabel right)
    (symbolMoveLocal_correct
      ((fixedBits w a).reverse.map SparseSymbol.bit) []) rfl state
    (compareResultStacks w a b base)
  simp only [List.length_map, List.length_reverse, fixedBits_length,
    List.append_nil, List.map_reverse, List.reverse_reverse] at hfirst
  rw [restoreFirst_bridge w a b base state] at hfirst
  let firstState := FullInterpreterState.moveLens.put state default
  let firstBase : CoreStack -> List SparseSymbol := fun
    | .accumulator => (fixedBits w a).map SparseSymbol.bit
    | .work2 => []
    | .work3 => (fixedBits w b).reverse.map SparseSymbol.bit
    | k => compareResultStacks w a b base k
  have hsecondRaw := run_lensPhase_to_right
    (symbolMoveCoreRenaming .work3 .work1 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel right
    (symbolMoveLocal_correct
      ((fixedBits w b).reverse.map SparseSymbol.bit) []) rfl
    firstState firstBase
  have hsecond' :
      ((fun o => o.bind (TM2.step
        (restoreComparedTailProgram returnLabel right)))^[w + 2])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work3 .work1 (by decide))
          FullInterpreterState.moveLens
          (symbolMoveLocalCfg .loop
            ((fixedBits w b).reverse.map SparseSymbol.bit) [])
          firstState firstBase)) =
      some (mapLabelCfg Sum.inr
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work3 .work1 (by decide))
          FullInterpreterState.moveLens returnLabel
          (symbolMoveLocalCfg .done []
            ((fixedBits w b).map SparseSymbol.bit))
          firstState firstBase)) := by
    simpa only [List.length_map, List.length_reverse, fixedBits_length,
      List.append_nil, List.map_reverse, List.reverse_reverse] using hsecondRaw
  dsimp [firstState, firstBase] at hsecond'
  have hchain := chain_liftRightProgram (m := w + 1 + 1) (n := w + 2)
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work2 .accumulator (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (restoreComparedTailProgram returnLabel right) hfirst hsecond'
  rw [restoreSecond_bridge returnLabel w a b base
    (FullInterpreterState.moveLens.put state default)] at hchain
  refine ⟨FullInterpreterState.moveLens.put firstState default, ?_⟩
  have htime : 2 * w + 4 = (w + 1 + 1) + (w + 1 + 1) := by omega
  rw [htime]
  simpa [restoreComparedProgram, firstState] using hchain

end Lax51Proofs.RamToTM
