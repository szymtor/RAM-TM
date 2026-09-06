import Lax51Proofs.RamToTM.ConditionalAccumulatorZero

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

abbrev ConditionalZeroTailLabel (R : Type) := Sum SymbolMoveLabel R
abbrev ConditionalZeroPhaseLabel (R : Type) :=
  Sum ConditionalZeroLabel (ConditionalZeroTailLabel R)

def conditionalZeroTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ConditionalZeroTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ConditionalZeroTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def conditionalZeroPhaseProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ConditionalZeroPhaseLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ConditionalZeroPhaseLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming (fullStateIdentityLens N)
      (conditionalZeroProgram N o) .done (Sum.inl SymbolMoveLabel.loop))
    (conditionalZeroTailProgram returnLabel right)

def conditionalZeroIntermediateStacks (w value : Nat) (zero : Bool)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    CoreStack -> List SparseSymbol
  | .work0 => conditionallyRewritten zero
      ((fixedBits w value).map SparseSymbol.bit)
  | .accumulator => []
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work1 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem conditionalZero_head_bridge {N : Nat} {R : Type}
    (o : Op) (w value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg coreIdentityRenaming (fullStateIdentityLens N)
      (Sum.inl SymbolMoveLabel.loop : ConditionalZeroTailLabel R)
      (conditionalZeroCfg .done
        (FullInterpreterState.moveLens.put state default) []
        (conditionallyRewritten (operandLiteralOversized o state)
          ((fixedBits w value).map SparseSymbol.bit))
        (operandBoundaryBase w value m base))
      state (operandBoundaryBase w value m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        (conditionallyRewritten (operandLiteralOversized o state)
          ((fixedBits w value).map SparseSymbol.bit)) [])
      (FullInterpreterState.moveLens.put state default)
      (conditionalZeroIntermediateStacks w value
        (operandLiteralOversized o state) m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, fullStateIdentityLens,
    conditionalZeroCfg, operandBoundaryBase, conditionalZeroIntermediateStacks,
    renamedStacks_coreIdentity, symbolMoveCoreRenaming,
    symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks, renamedStacks]
  constructor
  · rfl
  · funext k
    cases k <;> simp [conditionalZeroIntermediateStacks,
      operandBoundaryBase, symbolMoveCoreRenaming, symbolMoveCoreDecode,
      symbolMoveLocalCfg, symbolMoveStacks, renamedStacks]

theorem conditionallyRewritten_reverse (w value : Nat) (zero : Bool) :
    (conditionallyRewritten zero ((fixedBits w value).map SparseSymbol.bit)).reverse =
      (fixedBits w (if zero then 0 else value)).map SparseSymbol.bit := by
  cases zero
  · simp [conditionallyRewritten, List.map_reverse]
  · simp [conditionallyRewritten]

theorem conditionalZero_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w value : Nat) (zero : Bool) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens returnLabel
      (symbolMoveLocalCfg .done []
        (conditionallyRewritten zero
          ((fixedBits w value).map SparseSymbol.bit)).reverse)
      state (conditionalZeroIntermediateStacks w value zero m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (operandBoundaryBase w (if zero then 0 else value) m base) := by
  simp [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    symbolMoveCoreRenaming, symbolMoveCoreDecode, symbolMoveLocalCfg,
    symbolMoveStacks, conditionalZeroIntermediateStacks,
    operandBoundaryBase, renamedStacks, conditionallyRewritten_reverse]
  funext k
  cases k <;> simp [conditionalZeroIntermediateStacks, operandBoundaryBase,
    renamedStacks, symbolMoveCoreRenaming, symbolMoveCoreDecode,
    symbolMoveLocalCfg, symbolMoveStacks, conditionallyRewritten_reverse]

theorem conditionalZeroPhase_correct {N : Nat} {R : Type}
    (o : Op) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N)
    (hmove : FullInterpreterState.moveLens.get state = default) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (conditionalZeroPhaseProgram o returnLabel right)))^[2 * w + 4])
        (some (lensRenamedCfg coreIdentityRenaming (fullStateIdentityLens N)
          (conditionalZeroCfg .rewrite state
            ((fixedBits w value).map SparseSymbol.bit) []
            (operandBoundaryBase w value m base))
          state (operandBoundaryBase w value m base))) =
      some (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l : R => Sum.inr l)
          (cleanReturnCfg returnLabel finalState
            (operandBoundaryBase w
              (if operandLiteralOversized o state then 0 else value) m base)))) := by
  have hhead := run_lensPhase_to_right coreIdentityRenaming
    (fullStateIdentityLens N) (conditionalZeroProgram N o) .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (conditionalZeroTailProgram returnLabel right)
    (conditionalZero_correct o state
      ((fixedBits w value).map SparseSymbol.bit)
      (operandBoundaryBase w value m base) hmove) rfl
    state (operandBoundaryBase w value m base)
  simp only [List.length_map, fixedBits_length] at hhead
  rw [conditionalZero_head_bridge (R := R) o w value m base state] at hhead
  let headState := FullInterpreterState.moveLens.put state default
  let zero := operandLiteralOversized o state
  have htail := run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .accumulator (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel right
    (symbolMoveLocal_correct
      (conditionallyRewritten zero ((fixedBits w value).map SparseSymbol.bit)) [])
    rfl headState (conditionalZeroIntermediateStacks w value zero m base)
  have hrewriteLength :
      (conditionallyRewritten zero
        ((fixedBits w value).map SparseSymbol.bit)).length = w := by
    cases zero <;> simp [conditionallyRewritten]
  simp only [hrewriteLength, List.append_nil] at htail
  rw [conditionalZero_return_bridge returnLabel w value zero m base headState]
    at htail
  have hall := chain_liftRightProgram (m := w + 2) (n := w + 2)
    (lensPhaseLeft coreIdentityRenaming (fullStateIdentityLens N)
    (conditionalZeroProgram N o) .done (Sum.inl SymbolMoveLabel.loop))
    (conditionalZeroTailProgram returnLabel right) hhead htail
  rw [show 2 * w + 4 = (w + 2) + (w + 2) by omega]
  refine ⟨FullInterpreterState.moveLens.put headState default, ?_⟩
  simpa [conditionalZeroPhaseProgram, headState, zero] using hall

end Lax51Proofs.RamToTM
