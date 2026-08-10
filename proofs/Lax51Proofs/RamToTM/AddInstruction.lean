import Lax51Proofs.RamToTM.LoadInstruction

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax13.Ram

inductive AddResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev AddInstructionTailLabel (R : Type) :=
  Sum AddResetLabel (FullAddPhaseLabel R)

abbrev AddInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (AddInstructionTailLabel R)

def addResetProgram {N : Nat} {R : Type} : AddResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AddInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.macroLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl (Sum.inl SymbolMoveLabel.loop))

def addInstructionTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    AddInstructionTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (AddInstructionTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram addResetProgram (fullAddPhaseProgram returnLabel right)

def addInstructionProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    AddInstructionLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (AddInstructionLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl AddResetLabel.reset)
    (addInstructionTailProgram returnLabel right)

theorem addReset_step {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (addInstructionTailProgram returnLabel right)
      (cleanReturnCfg (Sum.inl AddResetLabel.reset)
        state (operandResultBase w a b m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
        (addInitialLocal w a b m base) state
        (operandResultBase w a b m base))) := by
  simp [addInstructionTailProgram, addResetProgram, cleanReturnCfg,
    mapLabelCfg, liftRightProgram, TM2.step, lensRenamedCfg,
    addInitialLocal, coreIdentityRenaming]
  constructor
  · rfl
  · constructor
    · rfl
    · funext k
      cases k <;> simp [addInitialLocal, lensRenamedCfg, renamedStacks,
        coreIdentityRenaming, addPipelineBase, operandBoundaryBase,
        operandResultBase, symbolMoveCoreRenaming, symbolMoveCoreDecode,
        symbolMoveLocalCfg, symbolMoveStacks, List.map_reverse]

def addInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 3 * w + 8

theorem addInstruction_correct {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= addInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (addInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := AddInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l : FullAddPhaseLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                ((a + operandWordValue w o m) % 2 ^ w) m base))))) := by
  rcases operandEval_correct o hN w a m hm
      (Sum.inl AddResetLabel.reset)
      (addInstructionTailProgram returnLabel right) state base with
    ⟨operandSteps, operandBound, operandState, hoperand⟩
  have hresetStep := addReset_step returnLabel right w a
    (operandWordValue w o m) m base operandState
  have hreset :
      ((fun x => x.bind (TM2.step
        (addInstructionTailProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl AddResetLabel.reset)
          operandState
          (operandResultBase w a (operandWordValue w o m) m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
          (addInitialLocal w a (operandWordValue w o m) m base)
          operandState
          (operandResultBase w a (operandWordValue w o m) m base))) := by
    simpa using hresetStep
  rcases fullAddPhase_correct returnLabel right w a
      (operandWordValue w o m) m base operandState with
    ⟨addState, hadd⟩
  have htail := chain_liftRightProgram addResetProgram
    (fullAddPhaseProgram returnLabel right) hreset hadd
  have hlift := transport_iterate_operand_right o
    (Sum.inl AddResetLabel.reset)
    (addInstructionTailProgram returnLabel right) htail
  have hchain := chain_loadInstruction_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (AddInstructionLabel o R) (FullInterpreterState N)) =>
      x.bind (TM2.step (addInstructionProgram o returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (3 * w + 7)), ?_, addState, ?_⟩
  · simp [addInstructionBound]
    omega
  · simpa [addInstructionProgram, addInstructionTailProgram] using hchain

end Lax51Proofs.RamToTM
