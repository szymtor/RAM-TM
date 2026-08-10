import Lax51Proofs.RamToTM.FullDivideMacro

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax13.Ram

abbrev DivideInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (FullDivideLabel R)

def divideInstructionProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideInstructionLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideInstructionLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl DividePrepareLabel.pushExtension)
    (fullDivideProgram returnLabel right)

def divideInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + divRunTimeBound w + 6 * w + 18

theorem divideInstruction_correct_of_operand_lt {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (ha : a < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hop : sparseValue w o m < 2 ^ w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= divideInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (divideInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := FullDivideLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (embedFullDivideReturnCfg
          (cleanReturnCfg returnLabel finalState
            (operandBoundaryBase w (a / sparseValue w o m) m base)))) := by
  rcases operandEval_correct o hN w a m hm
      (Sum.inl DividePrepareLabel.pushExtension)
      (fullDivideProgram returnLabel right) state base with
    ⟨operandSteps, operandBound, operandState, hoperand⟩
  let d := operandWordValue w o m
  have hd : d < 2 ^ w := operandWordValue_lt w o m
  have hdRaw : d = sparseValue w o m := Nat.mod_eq_of_lt hop
  by_cases hd0 : d = 0
  · have hdZero : operandWordValue w o m = 0 := by
      simpa [d] using hd0
    have hrawZero : sparseValue w o m = 0 := hdRaw.symm.trans hd0
    have hoperand' := hoperand
    rw [hdZero] at hoperand'
    rcases fullDivide_zero_correct returnLabel right w a m base operandState with
      ⟨divideState, _, _, hdivide⟩
    have hlift := transport_iterate_operand_right o
      (Sum.inl DividePrepareLabel.pushExtension)
      (fullDivideProgram returnLabel right) hdivide
    have hchain := chain_loadInstruction_iterations
      (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
          (DivideInstructionLabel o R) (FullInterpreterState N)) =>
        x.bind (TM2.step (divideInstructionProgram o returnLabel right)))
      hoperand' hlift
    refine ⟨operandSteps + (divZeroRunTime w + 6 * w + 18), ?_,
      divideState, ?_⟩
    · simp [divideInstructionBound]
      have hz := divZeroRunTime_le_bound w
      omega
    · simpa [divideInstructionProgram, hrawZero] using hchain
  · have hdPos : 0 < d := Nat.pos_of_ne_zero hd0
    rcases fullDivide_positive_correct returnLabel right w a d ha hdPos hd
        m base operandState with ⟨divideState, _, _, hdivide⟩
    have hlift := transport_iterate_operand_right o
      (Sum.inl DividePrepareLabel.pushExtension)
      (fullDivideProgram returnLabel right) hdivide
    have hchain := chain_loadInstruction_iterations
      (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
          (DivideInstructionLabel o R) (FullInterpreterState N)) =>
        x.bind (TM2.step (divideInstructionProgram o returnLabel right)))
      hoperand hlift
    refine ⟨operandSteps + (divPositiveRunTime w + 6 * w + 18), ?_,
      divideState, ?_⟩
    · simp [divideInstructionBound]
      have hp := divPositiveRunTime_le_bound w
      omega
    · simpa [divideInstructionProgram, hdRaw] using hchain

theorem divideInstruction_correct_nonliteral {N : Nat} {R : Type}
    (o : Op) (hNonliteral : match o with | .lit _ => False | _ => True)
    (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (ha : a < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= divideInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (divideInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := FullDivideLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (embedFullDivideReturnCfg
          (cleanReturnCfg returnLabel finalState
            (operandBoundaryBase w (a / sparseValue w o m) m base)))) := by
  cases o with
  | lit n => contradiction
  | mem address =>
      exact divideInstruction_correct_of_operand_lt (.mem address) hN
        returnLabel right w a ha m hm (sparseValue_mem_lt hm address) base state
  | ind address =>
      exact divideInstruction_correct_of_operand_lt (.ind address) hN
        returnLabel right w a ha m hm (sparseValue_ind_lt hm address) base state

end Lax51Proofs.RamToTM
