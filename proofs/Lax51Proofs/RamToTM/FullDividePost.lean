import Lax51Proofs.RamToTM.ConditionalAccumulatorZeroPhase

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

abbrev FullDividePostLabel (R : Type) :=
  FullDivideLabel (ConditionalZeroPhaseLabel R)

def fullDividePostProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullDividePostLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullDividePostLabel R)
      (FullInterpreterState N) :=
  fullDivideProgram (Sum.inl ConditionalZeroLabel.rewrite)
    (conditionalZeroPhaseProgram o returnLabel right)

theorem dividePost_start_bridge {N : Nat} {R : Type}
    (w value : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    cleanReturnCfg
        (Sum.inl ConditionalZeroLabel.rewrite : ConditionalZeroPhaseLabel R)
        state (operandBoundaryBase w value m base) =
      lensRenamedCfg coreIdentityRenaming (fullStateIdentityLens N)
        (conditionalZeroCfg .rewrite state
          ((fixedBits w value).map SparseSymbol.bit) []
          (operandBoundaryBase w value m base))
        state (operandBoundaryBase w value m base) := by
  simp [cleanReturnCfg, lensRenamedCfg, fullStateIdentityLens,
    conditionalZeroCfg, operandBoundaryBase, renamedStacks_coreIdentity]
  funext k
  cases k <;> rfl

theorem transport_iterate_fullDivide_right {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps : Nat}
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun : ((fun x => x.bind (TM2.step right))^[steps])
      (some c) = some d) :
    ((fun x => x.bind (TM2.step
      (fullDivideProgram returnLabel right)))^[steps])
      (some (embedFullDivideReturnCfg c)) =
    some (embedFullDivideReturnCfg d) := by
  have h1 := transport_iterate_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work2)
      FullInterpreterState.moveLens discardProgram .done returnLabel)
    right hrun
  have h2 := transport_iterate_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl DiscardLabel.loop))
    (divideCleanupFinalProgram returnLabel right) h1
  have h3 := transport_iterate_liftRightProgram
    (lensPhaseLeft preparedDivRenaming FullInterpreterState.divLens
      sparseDivCoreProgram .done (Sum.inl DiscardLabel.loop))
    (divideCleanupTailProgram returnLabel right) h2
  have h4 := transport_iterate_liftRightProgram
    (lensPhaseLeft divideZeroRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done (Sum.inl DivLabel.inspectDivisor))
    (fullDivideCleanProgram returnLabel right) h3
  have h5 := transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (divideZeroTailProgram returnLabel right) h4
  have h6 := transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (divideDividendTailProgram returnLabel right) h5
  have h7 := transport_iterate_liftRightProgram dividePrepareProgram
    (divideDivisorTailProgram returnLabel right) h6
  simpa [fullDivideProgram, divideDivisorTailProgram,
    divideDividendTailProgram, divideZeroTailProgram,
    fullDivideCleanProgram, divideCleanupTailProgram,
    divideCleanupFinalProgram, embedFullDivideReturnCfg] using h7

theorem fullDividePost_zero_correct {N : Nat} {R : Type}
    (o : Op) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (fullDividePostProgram o returnLabel right)))^[
          divZeroRunTime w + 8 * w + 22])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a 0 m base)))) =
      some (embedFullDivideReturnCfg
        (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w 0 m base))))) := by
  rcases fullDivide_zero_correct
      (Sum.inl ConditionalZeroLabel.rewrite : ConditionalZeroPhaseLabel R)
      (conditionalZeroPhaseProgram o returnLabel right)
      w a m base state with
    ⟨divideState, hmove, _, hdivide⟩
  rw [dividePost_start_bridge (R := R) w 0 m base divideState] at hdivide
  rcases conditionalZeroPhase_correct o returnLabel right w 0 m base
      divideState hmove with ⟨finalState, hpost⟩
  have hpostLift := transport_iterate_fullDivide_right
    (Sum.inl ConditionalZeroLabel.rewrite : ConditionalZeroPhaseLabel R)
    (conditionalZeroPhaseProgram o returnLabel right) hpost
  have hall := chain_loadInstruction_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (FullDividePostLabel R) (FullInterpreterState N)) =>
      x.bind (TM2.step (fullDividePostProgram o returnLabel right)))
    hdivide hpostLift
  refine ⟨finalState, ?_⟩
  have ht : divZeroRunTime w + 8 * w + 22 =
      (divZeroRunTime w + 6 * w + 18) + (2 * w + 4) := by omega
  rw [ht]
  simpa [fullDividePostProgram] using hall

theorem fullDividePost_positive_correct {N : Nat} {R : Type}
    (o : Op) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d : Nat) (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (fullDividePostProgram o returnLabel right)))^[
          divPositiveRunTime w + 8 * w + 22])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a d m base)))) =
      some (embedFullDivideReturnCfg
        (mapLabelCfg (fun l : ConditionalZeroTailLabel R => Sum.inr l)
          (mapLabelCfg (fun l : R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                (if operandLiteralOversized o state then 0 else a / d)
                m base))))) := by
  rcases fullDivide_positive_correct
      (Sum.inl ConditionalZeroLabel.rewrite : ConditionalZeroPhaseLabel R)
      (conditionalZeroPhaseProgram o returnLabel right)
      w a d ha hd0 hd m base state with
    ⟨divideState, hmove, hliteral, hdivide⟩
  rw [dividePost_start_bridge (R := R) w (a / d) m base divideState]
    at hdivide
  rcases conditionalZeroPhase_correct o returnLabel right w (a / d) m base
      divideState hmove with ⟨finalState, hpost⟩
  have hpostLift := transport_iterate_fullDivide_right
    (Sum.inl ConditionalZeroLabel.rewrite : ConditionalZeroPhaseLabel R)
    (conditionalZeroPhaseProgram o returnLabel right) hpost
  have hall := chain_loadInstruction_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
        (FullDividePostLabel R) (FullInterpreterState N)) =>
      x.bind (TM2.step (fullDividePostProgram o returnLabel right)))
    hdivide hpostLift
  refine ⟨finalState, ?_⟩
  have hover : operandLiteralOversized o divideState =
      operandLiteralOversized o state := by
    cases o <;> simp [operandLiteralOversized, hliteral]
  have ht : divPositiveRunTime w + 8 * w + 22 =
      (divPositiveRunTime w + 6 * w + 18) + (2 * w + 4) := by omega
  rw [ht]
  simpa [fullDividePostProgram, hover] using hall

end Lax51Proofs.RamToTM
