import Lax51Proofs.RamToTM.SubtractInstruction
import Lax51Proofs.RamToTM.DivideCoreMacro

namespace Lax51Proofs.RamToTM

open Turing TM2

def preparedDivEncode : DivStack -> CoreStack
  | .dividend => .work7
  | .divisor => .work1
  | .remainder => .work2
  | .quotient => .accumulator
  | .divisorBackup => .work3
  | .remainderBackup => .work4
  | .differenceReverse => .work5
  | .shiftTemp => .work6

def preparedDivDecode : CoreStack -> Option DivStack
  | .work7 => some .dividend
  | .work1 => some .divisor
  | .work2 => some .remainder
  | .accumulator => some .quotient
  | .work3 => some .divisorBackup
  | .work4 => some .remainderBackup
  | .work5 => some .differenceReverse
  | .work6 => some .shiftTemp
  | _ => none

def preparedDivRenaming : StackRenaming DivStack CoreStack where
  encode := preparedDivEncode
  decode := preparedDivDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;>
      simp [preparedDivDecode, preparedDivEncode] at h ⊢

abbrev FullDivideCoreLabel (R : Type) := Sum DivLabel R

def fullDivideCoreProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullDivideCoreLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullDivideCoreLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft preparedDivRenaming FullInterpreterState.divLens
      sparseDivCoreProgram .done returnLabel)
    right

def preparedDivideStacks (w a d : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .work7 => (fixedBits w a).reverse.map SparseSymbol.bit
  | .work1 => (fixedBits (w + 1) d).map SparseSymbol.bit
  | .work2 => (fixedBits (w + 1) 0).map SparseSymbol.bit
  | .accumulator | .work0 | .work3 | .work4 | .work5 | .work6 => []
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | k => base k

def divideCoreResultStacks (w d remainder quotient : Nat)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol) :
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w quotient).map SparseSymbol.bit
  | .work1 => (fixedBits (w + 1) d).map SparseSymbol.bit
  | .work2 => (fixedBits (w + 1) remainder).map SparseSymbol.bit
  | .work0 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | k => base k

theorem preparedDivide_initial_cfg {N : Nat} {R : Type}
    (w a d : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    lensRenamedCfg (Λx := R) preparedDivRenaming FullInterpreterState.divLens
      (sparseDivLocalInitialCfg (fixedBits w a).reverse
        (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
      state (preparedDivideStacks w a d m base) =
    lensRenamedCfg preparedDivRenaming FullInterpreterState.divLens
      (sparseDivLocalInitialCfg (fixedBits w a).reverse
        (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
      state (preparedDivideStacks w a d m base) := rfl

theorem divideCore_zero_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w a : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg preparedDivRenaming FullInterpreterState.divLens returnLabel
      (sparseDivLocalDoneCfg false (fixedBits (w + 1) 0)
        (fixedBits (w + 1) 0) (fixedBits w 0))
      state (preparedDivideStacks w a 0 m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.divLens.put state
        { (default : DivControl) with divisorNonzero := false })
      (divideCoreResultStacks w 0 0 0 m base) := by
  simp [phaseReturnCfg, cleanReturnCfg, sparseDivLocalDoneCfg,
    preparedDivideStacks, divideCoreResultStacks, renamedStacks,
    preparedDivRenaming, preparedDivDecode, divStacks, mapAlphabetStacks,
    sparseBitEncode]
  funext k
  cases k <;> simp [renamedStacks, preparedDivRenaming,
    preparedDivDecode, divStacks, mapAlphabetStacks, sparseBitEncode,
    divideCoreResultStacks, preparedDivideStacks]

theorem divideCore_positive_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w a d : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg preparedDivRenaming FullInterpreterState.divLens returnLabel
      (sparseDivLocalDoneCfg true (fixedBits (w + 1) d)
        (fixedBits (w + 1) (a % d)) (fixedBits w (a / d)))
      state (preparedDivideStacks w a d m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.divLens.put state
        { (default : DivControl) with divisorNonzero := true })
      (divideCoreResultStacks w d (a % d) (a / d) m base) := by
  simp [phaseReturnCfg, cleanReturnCfg, sparseDivLocalDoneCfg,
    preparedDivideStacks, divideCoreResultStacks, renamedStacks,
    preparedDivRenaming, preparedDivDecode, divStacks, mapAlphabetStacks,
    sparseBitEncode]
  funext k
  cases k <;> rfl

theorem fullDivideCore_zero_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    ((fun o => o.bind (TM2.step
      (fullDivideCoreProgram returnLabel right)))^[divZeroRunTime w + 1])
      (some (lensRenamedCfg preparedDivRenaming FullInterpreterState.divLens
        (sparseDivLocalInitialCfg (fixedBits w a).reverse
          (fixedBits (w + 1) 0) (fixedBits (w + 1) 0))
        state (preparedDivideStacks w a 0 m base))) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.divLens.put state
          { (default : DivControl) with divisorNonzero := false })
        (divideCoreResultStacks w 0 0 0 m base))) := by
  have h := run_lensPhase_to_right preparedDivRenaming
    FullInterpreterState.divLens sparseDivCoreProgram .done (by rfl)
    returnLabel right (sparseDivLocal_zero_correct w a) rfl state
    (preparedDivideStacks w a 0 m base)
  rw [divideCore_zero_return_bridge returnLabel w a m base state] at h
  simpa [fullDivideCoreProgram] using h

theorem fullDivideCore_positive_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d : Nat) (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w)
    (m : SparseMemory) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ((fun o => o.bind (TM2.step
      (fullDivideCoreProgram returnLabel right)))^[divPositiveRunTime w + 1])
      (some (lensRenamedCfg preparedDivRenaming FullInterpreterState.divLens
        (sparseDivLocalInitialCfg (fixedBits w a).reverse
          (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
        state (preparedDivideStacks w a d m base))) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.divLens.put state
          { (default : DivControl) with divisorNonzero := true })
        (divideCoreResultStacks w d (a % d) (a / d) m base))) := by
  have h := run_lensPhase_to_right preparedDivRenaming
    FullInterpreterState.divLens sparseDivCoreProgram .done (by rfl)
    returnLabel right (sparseDivLocal_positive_correct w a d ha hd0 hd) rfl
    state (preparedDivideStacks w a d m base)
  rw [divideCore_positive_return_bridge returnLabel w a d m base state] at h
  simpa [fullDivideCoreProgram] using h

end Lax51Proofs.RamToTM
