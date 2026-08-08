import Lax20Proofs.RamToTM.FullStoreMacro

namespace Lax20Proofs.RamToTM

open Turing TM2 Lax13.Ram

inductive StoreResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev StoreInstructionTailLabel (R : Type) :=
  Sum StoreResetLabel (FullStoreLabel R)

abbrev StoreInstructionLabel (address : Nat) (R : Type) :=
  OperandEvalLabel (.lit address) (StoreInstructionTailLabel R)

def storeResetProgram {N : Nat} {R : Type} : StoreResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (StoreInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.moveLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl CopyLabel.scan)

def storeInstructionTailProgram {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    StoreInstructionTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (StoreInstructionTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram storeResetProgram (fullStoreProgram returnLabel right)

def storeInstructionProgram {N : Nat} {R : Type} (address : Nat)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    StoreInstructionLabel address R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (StoreInstructionLabel address R)
      (FullInterpreterState N) :=
  operandEvalProgram (.lit address) (Sum.inl StoreResetLabel.reset)
    (storeInstructionTailProgram returnLabel right)

theorem storeReset_step {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w address accumulator : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (storeInstructionTailProgram returnLabel right)
      (cleanReturnCfg (Sum.inl StoreResetLabel.reset) state
        (operandResultBase w accumulator address m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg
        (copyCoreRenaming .accumulator .work1 .work7
          (by decide) (by decide) (by decide))
        FullInterpreterState.moveLens
        (copyCfg .scan ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        state (operandResultBase w accumulator address m base))) := by
  simp [storeInstructionTailProgram, storeResetProgram, cleanReturnCfg,
    liftRightProgram, mapLabelCfg, TM2.step, lensRenamedCfg, copyCfg,
    copyCfgState]
  have hs : renamedStacks
      (copyCoreRenaming .accumulator .work1 .work7
        (by decide) (by decide) (by decide))
      (copyStacks ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
      (operandResultBase w accumulator address m base) =
      operandResultBase w accumulator address m base := by
    funext k
    cases k <;> simp [renamedStacks, copyCoreRenaming, copyStacks,
      operandResultBase]
  rw [hs]

theorem SparseMemory.write_mod_address (w : Nat) (m : SparseMemory)
    (address value : Nat) :
    m.write w (address % 2 ^ w) value = m.write w address value := by
  simp [SparseMemory.write, Nat.mod_mod]

def storeInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 4 * w + 11

theorem storeInstruction_correct {N : Nat} {R : Type}
    (address : Nat) (hN : address <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator : Nat) (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= storeInstructionBound w m ∧ ∃ finalState,
      ((fun o => o.bind (TM2.step
        (storeInstructionProgram address returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := StoreInstructionTailLabel R) (.lit address) hN
          w accumulator m state base)) =
      some (embedOperandReturnCfg (.lit address)
        (mapLabelCfg (fun l : FullStoreLabel R => Sum.inr l)
          (mapLabelCfg (fun l : StorePrependTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l : FullPrependLabel R => Sum.inr l)
              (mapLabelCfg (fun l : R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (operandBoundaryBase w accumulator
                    (m.write w address accumulator) base))))))) := by
  rcases operandEval_correct (.lit address) hN w accumulator m hm
      (Sum.inl StoreResetLabel.reset)
      (storeInstructionTailProgram returnLabel right) state base with
    ⟨operandSteps, operandBound, operandState, hoperand⟩
  let wordAddress := operandWordValue w (.lit address) m
  have hresetStep := storeReset_step returnLabel right w wordAddress
    accumulator m base operandState
  have hreset :
      ((fun o => o.bind (TM2.step
        (storeInstructionTailProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl StoreResetLabel.reset) operandState
          (operandResultBase w accumulator wordAddress m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg
          (copyCoreRenaming .accumulator .work1 .work7
            (by decide) (by decide) (by decide))
          FullInterpreterState.moveLens
          (copyCfg .scan ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          operandState
          (operandResultBase w accumulator wordAddress m base))) := by
    simpa using hresetStep
  rcases fullStore_correct returnLabel right w wordAddress accumulator m base
      operandState with ⟨storeState, hstore⟩
  have htail := chain_liftRightProgram storeResetProgram
    (fullStoreProgram returnLabel right) hreset hstore
  have hlift := transport_iterate_operand_right (.lit address)
    (Sum.inl StoreResetLabel.reset)
    (storeInstructionTailProgram returnLabel right) htail
  have hchain := chain_loadInstruction_iterations
    (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (StoreInstructionLabel address R) (FullInterpreterState N)) =>
        o.bind (TM2.step (storeInstructionProgram address returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (4 * w + 10)), ?_, storeState, ?_⟩
  · simp [storeInstructionBound]
    omega
  · have hwrite : m.write w wordAddress accumulator =
        m.write w address accumulator := by
      simp [wordAddress, operandWordValue,
        SparseMemory.write_mod_address]
    rw [hwrite] at hchain
    simpa [storeInstructionProgram, storeInstructionTailProgram,
      wordAddress, operandWordValue] using hchain

end Lax20Proofs.RamToTM
