import Lax51Proofs.RamToTM.FullSubtractMacro

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax13.Ram

inductive SubtractResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev SubtractInstructionTailLabel (R : Type) :=
  Sum SubtractResetLabel (FullSubtractLabel R)

abbrev SubtractInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (SubtractInstructionTailLabel R)

def operandForcesSubtractionZero {N : Nat} (o : Op)
    (state : FullInterpreterState N) : Bool :=
  match o with
  | .lit _ => (FullInterpreterState.literalLens.get state).remaining.val != 0
  | .mem _ | .ind _ => false

def subtractResetProgram {N : Nat} {R : Type} (o : Op) : SubtractResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (SubtractInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.moveLens.put
        (FullInterpreterState.subLens.put
          { s with subtractForceZero := operandForcesSubtractionZero o s }
          default) default) <|
      .goto fun _ => Sum.inr (Sum.inl SymbolMoveLabel.loop)

def subtractInstructionTailProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    SubtractInstructionTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (SubtractInstructionTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram (subtractResetProgram o) (fullSubtractProgram returnLabel right)

def subtractInstructionProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    SubtractInstructionLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (SubtractInstructionLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl SubtractResetLabel.reset)
    (subtractInstructionTailProgram o returnLabel right)

theorem subtractReset_step {N : Nat} {R : Type}
    (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    TM2.step (subtractInstructionTailProgram o returnLabel right)
      (cleanReturnCfg (Sum.inl SubtractResetLabel.reset)
        state (operandResultBase w a b m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        FullInterpreterState.moveLens
        (symbolMoveLocalCfg .loop
          ((fixedBits w b).reverse.map SparseSymbol.bit) [])
        (FullInterpreterState.moveLens.put
          (FullInterpreterState.subLens.put
            { state with subtractForceZero := operandForcesSubtractionZero o state }
            default) default)
        (operandResultBase w a b m base))) := by
  simp [subtractInstructionTailProgram, subtractResetProgram,
    cleanReturnCfg, mapLabelCfg, liftRightProgram, TM2.step,
    lensRenamedCfg]
  constructor
  · rfl
  · constructor
    · rfl
    · funext k
      cases k <;> simp [symbolMoveCoreRenaming, symbolMoveCoreDecode,
        symbolMoveLocalCfg, symbolMoveStacks, renamedStacks,
        operandResultBase, List.map_reverse]

def subtractInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 3 * w + 8

theorem subtractInstruction_finish {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (ha : a < 2 ^ w)
    (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state operandState : FullInterpreterState N)
    (operandSteps : Nat) (operandBound : operandSteps <= operandEvalBound w m)
    (hoperand :
      ((fun x => x.bind (TM2.step
        (operandEvalProgram o (Sum.inl SubtractResetLabel.reset)
          (subtractInstructionTailProgram o returnLabel right))))^[operandSteps])
        (some (operandEvalStartCfg
          (R := SubtractInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (cleanReturnCfg (Sum.inl SubtractResetLabel.reset) operandState
          (operandResultBase w a (operandWordValue w o m) m base))))
    (force : Bool)
    (hforce : operandForcesSubtractionZero o operandState = force) :
    ∃ steps, steps <= subtractInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (subtractInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := SubtractInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l : FullSubtractLabel R => Sum.inr l)
          (mapLabelCfg (fun l : FullSubtractTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l : SubtractInstallPhaseLabel R => Sum.inr l)
              (mapLabelCfg (fun l : R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (operandBoundaryBase w
                    (if force then 0 else a - operandWordValue w o m)
                    m base))))))) := by
  let b := operandWordValue w o m
  have hb : b < 2 ^ w := operandWordValue_lt w o m
  have hresetStep := subtractReset_step o returnLabel right w a b m base
    operandState
  have hreset :
      ((fun x => x.bind (TM2.step
        (subtractInstructionTailProgram o returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl SubtractResetLabel.reset)
          operandState (operandResultBase w a b m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .work1 (by decide))
          FullInterpreterState.moveLens
          (symbolMoveLocalCfg .loop
            ((fixedBits w b).reverse.map SparseSymbol.bit) [])
          (FullInterpreterState.moveLens.put
          (FullInterpreterState.subLens.put
              { operandState with subtractForceZero :=
                operandForcesSubtractionZero o operandState } default) default)
          (operandResultBase w a b m base))) := by
    simpa using hresetStep
  rcases fullSubtract_correct returnLabel right w a b ha hb m base
      (FullInterpreterState.moveLens.put
        (FullInterpreterState.subLens.put
          { operandState with subtractForceZero :=
            operandForcesSubtractionZero o operandState } default) default)
      (by
        rw [subLens_get_moveLens_put,
          FullInterpreterState.subLens.get_put])
      force (by simpa using hforce) with
    ⟨subtractState, hsubtract⟩
  have htail := chain_liftRightProgram (subtractResetProgram o)
    (fullSubtractProgram returnLabel right) hreset hsubtract
  have hlift := transport_iterate_operand_right o
    (Sum.inl SubtractResetLabel.reset)
    (subtractInstructionTailProgram o returnLabel right) htail
  have hchain := chain_loadInstruction_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (SubtractInstructionLabel o R) (FullInterpreterState N)) =>
      x.bind (TM2.step (subtractInstructionProgram o returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (3 * w + 6)), ?_, subtractState, ?_⟩
  · simp [subtractInstructionBound]
    omega
  · simpa [subtractInstructionProgram, subtractInstructionTailProgram,
      b, subtractResultStacks] using hchain

theorem subtractInstruction_correct_of_operand_lt {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (ha : a < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hop : sparseValue w o m < 2 ^ w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= subtractInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (subtractInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := SubtractInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l : FullSubtractLabel R => Sum.inr l)
          (mapLabelCfg (fun l : FullSubtractTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l : SubtractInstallPhaseLabel R => Sum.inr l)
              (mapLabelCfg (fun l : R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (operandBoundaryBase w (a - sparseValue w o m) m base))))))) := by
  cases o with
  | lit n =>
      change n <= N at hN
      let operandState := FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w, by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
      have hoperand := literalOperand_correct n hN w a m
        (Sum.inl SubtractResetLabel.reset)
        (subtractInstructionTailProgram (.lit n) returnLabel right) state base
      have hbound : 2 * w + 3 <= operandEvalBound w m := by
        simp [operandEvalBound]
        omega
      have hnlt : n < 2 ^ w := by
        simpa [sparseValue, Op.value] using hop
      have hzero : n / 2 ^ w = 0 :=
        (literalWord_remaining_eq_zero_iff n w).2 hnlt
      have hfinish := subtractInstruction_finish (.lit n) hN returnLabel right
        w a ha m base state operandState (2 * w + 3) hbound
        (by simpa [operandEvalProgram, operandEvalStartCfg, operandArgument,
          embedOperandReturnCfg, operandState] using hoperand)
        false (by
          simp only [operandForcesSubtractionZero]
          change ((FullInterpreterState.literalLens.get operandState).remaining.val !=
            0) = false
          rw [show FullInterpreterState.literalLens.get operandState =
              ⟨none, ⟨n / 2 ^ w, by
                exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
            exact FullInterpreterState.literalLens.get_put _ _]
          simp [hzero])
      simpa [sparseValue, Op.value, operandWordValue,
        Nat.mod_eq_of_lt hnlt] using hfinish
  | mem address =>
      rcases operandEval_correct (.mem address) hN w a m hm
          (Sum.inl SubtractResetLabel.reset)
          (subtractInstructionTailProgram (.mem address) returnLabel right)
          state base with ⟨steps, hsteps, operandState, hoperand⟩
      have hfinish := subtractInstruction_finish (.mem address) hN
        returnLabel right w a ha m base state operandState steps hsteps hoperand
        false (by rfl)
      simpa [operandWordValue, Nat.mod_eq_of_lt hop] using hfinish
  | ind address =>
      rcases operandEval_correct (.ind address) hN w a m hm
          (Sum.inl SubtractResetLabel.reset)
          (subtractInstructionTailProgram (.ind address) returnLabel right)
          state base with ⟨steps, hsteps, operandState, hoperand⟩
      have hfinish := subtractInstruction_finish (.ind address) hN
        returnLabel right w a ha m base state operandState steps hsteps hoperand
        false (by rfl)
      simpa [operandWordValue, Nat.mod_eq_of_lt hop] using hfinish

theorem subtractInstruction_correct {N : Nat} {R : Type}
    (o : Op) (hN : operandArgument o <= N)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (ha : a < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ steps, steps <= subtractInstructionBound w m ∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (subtractInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R := SubtractInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l : FullSubtractLabel R => Sum.inr l)
          (mapLabelCfg (fun l : FullSubtractTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l : SubtractInstallPhaseLabel R => Sum.inr l)
              (mapLabelCfg (fun l : R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (operandBoundaryBase w (a - sparseValue w o m) m base))))))) := by
  cases o with
  | mem address =>
      exact subtractInstruction_correct_of_operand_lt (.mem address) hN
        returnLabel right w a ha m hm (sparseValue_mem_lt hm address)
        base state
  | ind address =>
      exact subtractInstruction_correct_of_operand_lt (.ind address) hN
        returnLabel right w a ha m hm (sparseValue_ind_lt hm address)
        base state
  | lit n =>
      by_cases hnlt : n < 2 ^ w
      · apply subtractInstruction_correct_of_operand_lt (.lit n) hN
          returnLabel right w a ha m hm
        simpa [sparseValue, Op.value] using hnlt
      · change n <= N at hN
        let operandState := FullInterpreterState.literalLens.put state
          ⟨none, ⟨n / 2 ^ w, by
            exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
        have hoperand := literalOperand_correct n hN w a m
          (Sum.inl SubtractResetLabel.reset)
          (subtractInstructionTailProgram (.lit n) returnLabel right) state base
        have hbound : 2 * w + 3 <= operandEvalBound w m := by
          simp [operandEvalBound]
          omega
        have hquot : n / 2 ^ w ≠ 0 := by
          intro hz
          exact hnlt ((literalWord_remaining_eq_zero_iff n w).1 hz)
        have hfinish := subtractInstruction_finish (.lit n) hN returnLabel right
          w a ha m base state operandState (2 * w + 3) hbound
          (by simpa [operandEvalProgram, operandEvalStartCfg, operandArgument,
            embedOperandReturnCfg, operandState] using hoperand)
          true (by
            simp only [operandForcesSubtractionZero]
            change ((FullInterpreterState.literalLens.get operandState).remaining.val !=
              0) = true
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w, by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hquot])
        have hle : a <= n := le_trans (Nat.le_of_lt ha) (Nat.le_of_not_gt hnlt)
        have hsub : a - n = 0 := Nat.sub_eq_zero_of_le hle
        simpa [sparseValue, Op.value, hsub] using hfinish

end Lax51Proofs.RamToTM
