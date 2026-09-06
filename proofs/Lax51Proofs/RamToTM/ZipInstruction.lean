import Lax51Proofs.RamToTM.FullZipMacro

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

inductive ZipResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev ZipInstructionTailLabel (R : Type) :=
  Sum ZipResetLabel (FullZipPhaseLabel R)

abbrev ZipInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (ZipInstructionTailLabel R)

def zipResetProgram {N : Nat} {R : Type} : ZipResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ZipInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.macroLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl (Sum.inl SymbolMoveLabel.loop))

def zipInstructionTailProgram {N : Nat} {R : Type}
    (f : Bool -> Bool -> Bool) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ZipInstructionTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ZipInstructionTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram zipResetProgram (fullZipPhaseProgram f returnLabel right)

def zipInstructionProgram {N : Nat} {R : Type} (f : Bool -> Bool -> Bool)
    (o : Op) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ZipInstructionLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ZipInstructionLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl ZipResetLabel.reset)
    (zipInstructionTailProgram f returnLabel right)

theorem zipReset_step {N : Nat} {R : Type}
    (f : Bool -> Bool -> Bool) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (zipInstructionTailProgram f returnLabel right)
      (cleanReturnCfg (Sum.inl ZipResetLabel.reset)
        state (operandResultBase w a b m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
        (zipInitialLocal f w a b m base) state
        (operandResultBase w a b m base))) := by
  simp [zipInstructionTailProgram, zipResetProgram, cleanReturnCfg,
    mapLabelCfg, liftRightProgram, TM2.step, lensRenamedCfg,
    zipInitialLocal, coreIdentityRenaming]
  constructor
  · rfl
  · constructor
    · rfl
    · funext k
      cases k <;> simp [zipInitialLocal, lensRenamedCfg, renamedStacks,
        coreIdentityRenaming, zipPipelineBase, operandBoundaryBase,
        operandResultBase, symbolMoveCoreRenaming, symbolMoveCoreDecode,
        symbolMoveLocalCfg, symbolMoveStacks, List.map_reverse]

def zipInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 3 * w + 8

theorem zipInstruction_correct {N : Nat} {R : Type}
    (f : Bool -> Bool -> Bool) (o : Op) (hN : operandArgument o <= N)
    (w a result : Nat) (m : SparseMemory)
    (hresult : fixedBits w result =
      zipBits f (fixedBits w a) (fixedBits w (operandWordValue w o m)))
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= zipInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (zipInstructionProgram f o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := ZipInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l : FullZipPhaseLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w (result % 2 ^ w) m base))))) := by
  rcases operandEval_correct o hN w a m hm
      (Sum.inl ZipResetLabel.reset)
      (zipInstructionTailProgram f returnLabel right) state base with
    ⟨operandSteps, operandBound, operandState, hoperand⟩
  have hresetStep := zipReset_step f returnLabel right w a
    (operandWordValue w o m) m base operandState
  have hreset :
      ((fun x => x.bind (TM2.step
        (zipInstructionTailProgram f returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl ZipResetLabel.reset)
          operandState
          (operandResultBase w a (operandWordValue w o m) m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
          (zipInitialLocal f w a (operandWordValue w o m) m base)
          operandState
          (operandResultBase w a (operandWordValue w o m) m base))) := by
    simpa using hresetStep
  rcases fullZipPhase_correct f w a (operandWordValue w o m) result hresult
      returnLabel right m base operandState with ⟨zipState, hzip⟩
  have htail := chain_liftRightProgram zipResetProgram
    (fullZipPhaseProgram f returnLabel right) hreset hzip
  have hlift := transport_iterate_operand_right o
    (Sum.inl ZipResetLabel.reset)
    (zipInstructionTailProgram f returnLabel right) htail
  have hchain := chain_loadInstruction_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (ZipInstructionLabel o R) (FullInterpreterState N)) =>
      x.bind (TM2.step (zipInstructionProgram f o returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (3 * w + 7)), ?_, zipState, ?_⟩
  · simp [zipInstructionBound]
    omega
  · simpa [zipInstructionProgram, zipInstructionTailProgram] using hchain

inductive BitwiseKind
  | and | or | xor | compl
  deriving DecidableEq, Fintype, Inhabited

def BitwiseKind.boolFn : BitwiseKind -> Bool -> Bool -> Bool
  | .and => fun a b => a && b
  | .or => fun a b => a || b
  | .xor => Bool.xor
  | .compl => fun a _ => !a

def BitwiseKind.natFn (w : Nat) : BitwiseKind -> Nat -> Nat -> Nat
  | .and => Nat.land
  | .or => Nat.lor
  | .xor => Nat.xor
  | .compl => fun a _ => 2 ^ w - 1 - a % 2 ^ w

theorem fixedBits_bitwiseKind (kind : BitwiseKind) (w a b : Nat) :
    fixedBits w (kind.natFn w a b) =
      zipBits kind.boolFn (fixedBits w a) (fixedBits w b) := by
  cases kind with
  | and => exact fixedBits_land w a b
  | or => exact fixedBits_lor w a b
  | xor => exact fixedBits_xor w a b
  | compl => exact fixedBits_complement w a b

def bitwiseInstructionProgram {N : Nat} {R : Type} (kind : BitwiseKind)
    (o : Op) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  zipInstructionProgram kind.boolFn o returnLabel right

theorem bitwiseInstruction_correct {N : Nat} {R : Type}
    (kind : BitwiseKind) (o : Op) (hN : operandArgument o <= N)
    (w a : Nat) (m : SparseMemory) (hm : m.Normalized w)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= zipInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (bitwiseInstructionProgram kind o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := ZipInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l : FullZipPhaseLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                (kind.natFn w a (operandWordValue w o m) % 2 ^ w)
                m base))))) := by
  simpa [bitwiseInstructionProgram] using
    zipInstruction_correct kind.boolFn o hN w a
      (kind.natFn w a (operandWordValue w o m)) m
      (fixedBits_bitwiseKind kind w a (operandWordValue w o m))
      returnLabel right hm base state

end Lax51Proofs.RamToTM
