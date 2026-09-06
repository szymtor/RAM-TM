import Lax51Proofs.RamToTM.FullDividePost

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

abbrev DivideInstructionTotalLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (FullDividePostLabel R)

def divideInstructionTotalProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideInstructionTotalLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideInstructionTotalLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl DividePrepareLabel.pushExtension)
    (fullDividePostProgram o returnLabel right)

def divideInstructionTotalBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + divRunTimeBound w + 8 * w + 22

theorem divideInstructionTotal_finish {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (ha : a < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state operandState : FullInterpreterState N)
    (operandSteps : Nat) (operandBound : operandSteps <= operandEvalBound w m)
    (hoperand :
      ((fun x => x.bind (TM2.step
        (divideInstructionTotalProgram o returnLabel right)))^[operandSteps])
        (some (operandEvalStartCfg
          (R := FullDividePostLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension operandState
            (operandResultBase w a (operandWordValue w o m) m base)))))
    (hsemantic :
      (if operandLiteralOversized o operandState then 0
        else a / operandWordValue w o m) = a / sparseValue w o m) :
    ∃ steps, steps <= divideInstructionTotalBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (divideInstructionTotalProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := FullDividePostLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (embedFullDivideReturnCfg
          (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w (a / sparseValue w o m) m base)))))) := by
  let d := operandWordValue w o m
  have hd : d < 2 ^ w := operandWordValue_lt w o m
  by_cases hd0 : d = 0
  · have hoperandZero := hoperand
    rw [show operandWordValue w o m = d by rfl, hd0] at hoperandZero
    have hdivide := fullDividePost_zero_correct o returnLabel right
      w a m base operandState
    have hlift := transport_iterate_operand_right o
      (Sum.inl DividePrepareLabel.pushExtension)
      (fullDividePostProgram o returnLabel right) hdivide.choose_spec
    have hchain := chain_loadInstruction_iterations
      (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
          (DivideInstructionTotalLabel o R) (FullInterpreterState N)) =>
        x.bind (TM2.step (divideInstructionTotalProgram o returnLabel right)))
      hoperandZero hlift
    refine ⟨operandSteps + (divZeroRunTime w + 8 * w + 22), ?_,
      hdivide.choose, ?_⟩
    · simp [divideInstructionTotalBound]
      have hz := divZeroRunTime_le_bound w
      omega
    · have hresult : a / sparseValue w o m = 0 := by
        have hs := hsemantic
        simp [d, hd0] at hs
        exact hs.symm
      simpa [divideInstructionTotalProgram, hresult] using hchain
  · have hdPos : 0 < d := Nat.pos_of_ne_zero hd0
    rcases fullDividePost_positive_correct o returnLabel right
        w a d ha hdPos hd m base operandState with
      ⟨divideState, hdivide⟩
    have hlift := transport_iterate_operand_right o
      (Sum.inl DividePrepareLabel.pushExtension)
      (fullDividePostProgram o returnLabel right) hdivide
    have hchain := chain_loadInstruction_iterations
      (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
          (DivideInstructionTotalLabel o R) (FullInterpreterState N)) =>
        x.bind (TM2.step (divideInstructionTotalProgram o returnLabel right)))
      (by simpa [d] using hoperand) hlift
    refine ⟨operandSteps + (divPositiveRunTime w + 8 * w + 22), ?_,
      divideState, ?_⟩
    · simp [divideInstructionTotalBound]
      have hp := divPositiveRunTime_le_bound w
      omega
    · simpa [divideInstructionTotalProgram, d, hsemantic] using hchain

theorem divideInstructionTotal_correct {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (ha : a < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= divideInstructionTotalBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (divideInstructionTotalProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := FullDividePostLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (embedFullDivideReturnCfg
          (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l : R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w (a / sparseValue w o m) m base)))))) := by
  cases o with
  | mem address =>
      rcases operandEval_correct (.mem address) hN w a m hm
          (Sum.inl DividePrepareLabel.pushExtension)
          (fullDividePostProgram (.mem address) returnLabel right)
          state base with ⟨steps, hsteps, operandState, hoperand⟩
      apply divideInstructionTotal_finish (.mem address) hN returnLabel right
        w a ha m base state operandState steps hsteps
      · simpa [divideInstructionTotalProgram] using hoperand
      · simp [operandLiteralOversized, operandWordValue,
          Nat.mod_eq_of_lt (sparseValue_mem_lt hm address)]
  | ind address =>
      rcases operandEval_correct (.ind address) hN w a m hm
          (Sum.inl DividePrepareLabel.pushExtension)
          (fullDividePostProgram (.ind address) returnLabel right)
          state base with ⟨steps, hsteps, operandState, hoperand⟩
      apply divideInstructionTotal_finish (.ind address) hN returnLabel right
        w a ha m base state operandState steps hsteps
      · simpa [divideInstructionTotalProgram] using hoperand
      · simp [operandLiteralOversized, operandWordValue,
          Nat.mod_eq_of_lt (sparseValue_ind_lt hm address)]
  | lit n =>
      change n <= N at hN
      let operandState := FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w, by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
      have hoperand := literalOperand_correct n hN w a m
        (Sum.inl DividePrepareLabel.pushExtension)
        (fullDividePostProgram (.lit n) returnLabel right) state base
      have hbound : 2 * w + 3 <= operandEvalBound w m := by
        simp [operandEvalBound]
        omega
      apply divideInstructionTotal_finish (.lit n) hN returnLabel right
        w a ha m base state operandState (2 * w + 3) hbound
      · simpa [divideInstructionTotalProgram, operandEvalStartCfg,
          operandArgument, embedOperandReturnCfg, operandState] using hoperand
      · by_cases hnlt : n < 2 ^ w
        · have hzero : n / 2 ^ w = 0 :=
            (literalWord_remaining_eq_zero_iff n w).2 hnlt
          have hover : operandLiteralOversized (.lit n) operandState = false := by
            simp only [operandLiteralOversized]
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w, by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hzero]
          simp [hover, operandWordValue, sparseValue, Op.value,
            Nat.mod_eq_of_lt hnlt]
        · have hquot : n / 2 ^ w ≠ 0 := by
            intro hz
            exact hnlt ((literalWord_remaining_eq_zero_iff n w).1 hz)
          have han : a < n := lt_of_lt_of_le ha (Nat.le_of_not_gt hnlt)
          have hover : operandLiteralOversized (.lit n) operandState = true := by
            simp only [operandLiteralOversized]
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w, by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hquot]
          simp [hover, sparseValue, Op.value, Nat.div_eq_of_lt han]

end Lax51Proofs.RamToTM
