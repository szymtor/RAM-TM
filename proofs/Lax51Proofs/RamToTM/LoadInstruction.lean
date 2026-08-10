import Lax51Proofs.RamToTM.FullLoadMacro

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax13.Ram

inductive LoadResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev LoadInstructionTailLabel (R : Type) :=
  Sum LoadResetLabel (FullLoadLabel R)

abbrev LoadInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (LoadInstructionTailLabel R)

def loadResetProgram {N : Nat} {R : Type} : LoadResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (LoadInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.macroLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl (Sum.inl SymbolMoveLabel.loop))

def loadInstructionTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    LoadInstructionTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (LoadInstructionTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram loadResetProgram (fullLoadProgram returnLabel right)

def loadInstructionProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    LoadInstructionLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (LoadInstructionLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl LoadResetLabel.reset)
    (loadInstructionTailProgram returnLabel right)

def loadInitialLocal (w old value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      ClosedAccInstallLabel InterpreterMacroState :=
  lensRenamedCfg (Λx := AccInstallTailLabel Unit)
    (symbolMoveCoreRenaming .accumulator .work7 (by decide))
    InterpreterMacroState.moveLens
    (symbolMoveLocalCfg .loop ((fixedBits w old).map SparseSymbol.bit) [])
    default
    (accInstallBase (fixedBits w old) (fixedBits w value)
      (operandBoundaryBase w old m base))

theorem loadReset_step {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w old value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (loadInstructionTailProgram returnLabel right)
      (cleanReturnCfg (Sum.inl LoadResetLabel.reset)
        state (operandResultBase w old value m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
        (loadInitialLocal w old value m base) state
        (operandResultBase w old value m base))) := by
  simp [loadInstructionTailProgram, loadResetProgram, cleanReturnCfg,
    mapLabelCfg, liftRightProgram, TM2.step, lensRenamedCfg,
    loadInitialLocal, coreIdentityRenaming, renamedStacks_coreIdentity]
  constructor
  · rfl
  · constructor
    · rfl
    · funext k
      cases k <;> simp [loadInitialLocal, lensRenamedCfg, renamedStacks,
        coreIdentityRenaming, accInstallBase, operandBoundaryBase,
        operandResultBase, symbolMoveCoreRenaming, symbolMoveCoreDecode,
        symbolMoveLocalCfg, symbolMoveStacks, List.map_reverse]

theorem chain_loadInstruction_iterations {X : Type} (step : X -> X)
    {a b c : X} {m n : Nat}
    (h1 : (step^[m]) a = b) (h2 : (step^[n]) b = c) :
    (step^[m + n]) a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

def loadInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 3 * w + 8

theorem loadInstruction_correct {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w old : Nat) (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= loadInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (loadInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := LoadInstructionTailLabel R) o hN w old m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l : FullLoadLabel R => Sum.inr l)
          (mapLabelCfg (fun l : FullLoadFinishLabel R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w (operandWordValue w o m) m base)))))) := by
  rcases operandEval_correct o hN w old m hm
      (Sum.inl LoadResetLabel.reset)
      (loadInstructionTailProgram returnLabel right) state base with
    ⟨operandSteps, operandBound, operandState, hoperand⟩
  have hresetStep := loadReset_step returnLabel right w old
    (operandWordValue w o m) m base operandState
  have hreset :
      ((fun x => x.bind (TM2.step
        (loadInstructionTailProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl LoadResetLabel.reset)
          operandState
          (operandResultBase w old (operandWordValue w o m) m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg coreIdentityRenaming
          FullInterpreterState.macroLens
          (loadInitialLocal w old (operandWordValue w o m) m base)
          operandState
          (operandResultBase w old (operandWordValue w o m) m base))) := by
    simpa using hresetStep
  rcases fullLoadMacro_correct returnLabel right w old
      (operandWordValue w o m) m base operandState with
    ⟨loadState, hload⟩
  have htail := chain_liftRightProgram loadResetProgram
    (fullLoadProgram returnLabel right) hreset hload
  have hlift := transport_iterate_operand_right o
    (Sum.inl LoadResetLabel.reset)
    (loadInstructionTailProgram returnLabel right) htail
  have hchain := chain_loadInstruction_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (LoadInstructionLabel o R) (FullInterpreterState N)) =>
      x.bind (TM2.step (loadInstructionProgram o returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (3 * w + 7)), ?_, loadState, ?_⟩
  · simp [loadInstructionBound]
    omega
  · simpa [loadInstructionProgram, loadInstructionTailProgram] using hchain

end Lax51Proofs.RamToTM
