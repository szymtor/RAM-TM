import Lax51Proofs.RamToTM.FullMultiplyMacro

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

inductive MulResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev MulInstructionTailLabel (R : Type) :=
  Sum MulResetLabel (FullMulLabel R)

abbrev MulInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (MulInstructionTailLabel R)

def mulResetProgram {N : Nat} {R : Type} : MulResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.macroLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl (Sum.inl SymbolMoveLabel.loop))

noncomputable def mulInstructionTailProgram {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram mulResetProgram (fullMulProgram returnLabel right)

noncomputable def mulInstructionProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  operandEvalProgram o (Sum.inl MulResetLabel.reset)
    (mulInstructionTailProgram returnLabel right)

theorem mulReset_step {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (mulInstructionTailProgram returnLabel right)
      (cleanReturnCfg (Sum.inl MulResetLabel.reset)
        state (operandResultBase w a b m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
        (mulInitialLocal w a b m base) state
        (operandResultBase w a b m base))) := by
  simp [mulInstructionTailProgram, mulResetProgram, cleanReturnCfg,
    mapLabelCfg, liftRightProgram, TM2.step, lensRenamedCfg,
    mulInitialLocal, coreIdentityRenaming]
  constructor
  · rfl
  · constructor
    · rfl
    · funext k
      cases k <;> simp [mulInitialLocal, lensRenamedCfg, renamedStacks,
        coreIdentityRenaming, mulPipelineBase, operandBoundaryBase,
        operandResultBase, symbolMoveCoreRenaming, symbolMoveCoreDecode,
        symbolMoveLocalCfg, symbolMoveStacks, List.map_reverse]

def mulInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + w * (5 * w + 8) + 7 * w + 17

theorem mulInstruction_correct {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (hw : 0 < w)
    (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= mulInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (mulInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := MulInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l : FullMulLabel R => Sum.inr l)
          (mapLabelCfg (fun l : FullMulFinishLabel R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w
                  ((a * operandWordValue w o m) % 2 ^ w) m base)))))) := by
  have hb := operandWordValue_lt w o m
  rcases operandEval_correct o hN w a m hm
      (Sum.inl MulResetLabel.reset)
      (mulInstructionTailProgram returnLabel right) state base with
    ⟨operandSteps, operandBound, operandState, hoperand⟩
  have hresetStep := mulReset_step returnLabel right w a
    (operandWordValue w o m) m base operandState
  have hreset :
      ((fun x => x.bind (TM2.step
        (mulInstructionTailProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl MulResetLabel.reset)
          operandState
          (operandResultBase w a (operandWordValue w o m) m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
          (mulInitialLocal w a (operandWordValue w o m) m base)
          operandState
          (operandResultBase w a (operandWordValue w o m) m base))) := by
    simpa using hresetStep
  rcases fullMul_correct returnLabel right w a (operandWordValue w o m)
      hw hb m base operandState with ⟨mulState, hmul⟩
  have htail := chain_liftRightProgram mulResetProgram
    (fullMulProgram returnLabel right) hreset hmul
  have hlift := transport_iterate_operand_right o
    (Sum.inl MulResetLabel.reset)
    (mulInstructionTailProgram returnLabel right) htail
  have hchain := chain_loadInstruction_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (MulInstructionLabel o R) (FullInterpreterState N)) =>
      x.bind (TM2.step (mulInstructionProgram o returnLabel right)))
    hoperand hlift
  let mulSteps := mulRunTime (fixedBits w (operandWordValue w o m)) w +
    7 * w + 15
  refine ⟨operandSteps + (1 + mulSteps), ?_, mulState, ?_⟩
  · have hrun := mulMachine_fixed_time_le w (operandWordValue w o m)
    simp [mulInstructionBound, mulSteps]
    omega
  · simpa [mulInstructionProgram, mulInstructionTailProgram, mulSteps]
      using hchain

end Lax51Proofs.RamToTM
