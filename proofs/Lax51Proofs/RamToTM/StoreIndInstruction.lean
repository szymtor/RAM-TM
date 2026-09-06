import Lax51Proofs.RamToTM.StoreInstruction

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

abbrev StoreIndInstructionLabel (address : Nat) (R : Type) :=
  OperandEvalLabel (.mem address) (StoreInstructionTailLabel R)

def storeIndInstructionProgram {N : Nat} {R : Type} (address : Nat)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    StoreIndInstructionLabel address R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (StoreIndInstructionLabel address R)
      (FullInterpreterState N) :=
  operandEvalProgram (.mem address) (Sum.inl StoreResetLabel.reset)
    (storeInstructionTailProgram returnLabel right)

def storeIndInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 4 * w + 11

theorem storeIndInstruction_correct {N : Nat} {R : Type}
    (address : Nat) (hN : address <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator : Nat) (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= storeIndInstructionBound w m ∧ ∃ finalState,
      ((fun o => o.bind (TM2.step
        (storeIndInstructionProgram address returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := StoreInstructionTailLabel R) (.mem address) hN
          w accumulator m state base)) =
      some (embedOperandReturnCfg (.mem address)
        (mapLabelCfg (fun l : FullStoreLabel R => Sum.inr l)
          (mapLabelCfg (fun l : StorePrependTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l : FullPrependLabel R => Sum.inr l)
              (mapLabelCfg (fun l : R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (operandBoundaryBase w accumulator
                    (m.write w (m.read (address % 2 ^ w)) accumulator)
                    base))))))) := by
  rcases operandEval_correct (.mem address) hN w accumulator m hm
      (Sum.inl StoreResetLabel.reset)
      (storeInstructionTailProgram returnLabel right) state base with
    ⟨operandSteps, operandBound, operandState, hoperand⟩
  let wordAddress := operandWordValue w (.mem address) m
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
  have hlift := transport_iterate_operand_right (.mem address)
    (Sum.inl StoreResetLabel.reset)
    (storeInstructionTailProgram returnLabel right) htail
  have hchain := chain_loadInstruction_iterations
    (fun o : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (StoreIndInstructionLabel address R) (FullInterpreterState N)) =>
        o.bind (TM2.step (storeIndInstructionProgram address returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (4 * w + 10)), ?_, storeState, ?_⟩
  · simp [storeIndInstructionBound]
    omega
  · have hwrite : m.write w wordAddress accumulator =
        m.write w (m.read (address % 2 ^ w)) accumulator := by
      simp [wordAddress, SparseMemory.write_mod_address]
    rw [hwrite] at hchain
    simpa [storeIndInstructionProgram, storeInstructionTailProgram,
      wordAddress] using hchain

end Lax51Proofs.RamToTM
