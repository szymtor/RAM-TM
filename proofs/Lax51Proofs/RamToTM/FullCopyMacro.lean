import Lax51Proofs.RamToTM.CopyStackMacro

namespace Lax51Proofs.RamToTM

open Turing TM2

abbrev FullCopyLabel (R : Type) := Sum CopyLabel R

def fullCopyProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullCopyLabel R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (FullCopyLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
        (by decide))
      FullInterpreterState.moveLens copyProgram .done returnLabel)
    right

def copyAccumulatorStacks (xs : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .accumulator => xs
  | .work1 => xs.reverse
  | .work7 => []
  | k => base k

theorem fullCopy_generic_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (xs : List SparseSymbol)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg
      (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
        (by decide))
      FullInterpreterState.moveLens returnLabel
      (copyCfg .done xs xs.reverse []) state base =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (copyAccumulatorStacks xs base) := by
  simp only [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg, copyCfg,
    copyCfgState]
  have hs :
      renamedStacks
        (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
          (by decide))
        (copyStacks xs xs.reverse []) base = copyAccumulatorStacks xs base := by
    funext k
    cases k <;> simp [renamedStacks, copyCoreRenaming, copyStacks,
      copyAccumulatorStacks]
  rw [hs]

theorem fullCopyAccumulator_generic_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (xs : List SparseSymbol) (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ((fun o => o.bind (TM2.step (fullCopyProgram returnLabel right)))^[
      2 * xs.length + 3])
      (some (lensRenamedCfg
        (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
          (by decide))
        FullInterpreterState.moveLens (copyCfg .scan xs [] []) state base)) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.moveLens.put state default)
        (copyAccumulatorStacks xs base))) := by
  have h := run_lensPhase_to_right
    (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
      (by decide))
    FullInterpreterState.moveLens copyProgram .done (by rfl) returnLabel right
    (copy_correct xs []) rfl state base
  simp only [List.append_nil] at h
  rw [fullCopy_generic_return_bridge returnLabel xs base state] at h
  simpa [fullCopyProgram] using h

def copyAccumulatorResultBase (w accumulator : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) :
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work1 => ((fixedBits w accumulator).map SparseSymbol.bit).reverse
  | .input => base .input
  | .output => base .output
  | _ => []

theorem fullCopy_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w accumulator : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg
      (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
        (by decide))
      FullInterpreterState.moveLens returnLabel
      (copyCfg .done ((fixedBits w accumulator).map SparseSymbol.bit)
        (((fixedBits w accumulator).map SparseSymbol.bit).reverse) [])
      state (operandBoundaryBase w accumulator m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (copyAccumulatorResultBase w accumulator m base) := by
  simp only [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg, copyCfg,
    copyCfgState]
  have hs :
      renamedStacks
        (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
          (by decide))
        (copyStacks ((fixedBits w accumulator).map SparseSymbol.bit)
          ((fixedBits w accumulator).map SparseSymbol.bit).reverse [])
        (operandBoundaryBase w accumulator m base) =
      copyAccumulatorResultBase w accumulator m base := by
    funext k
    cases k <;> simp [renamedStacks, copyCoreRenaming, copyStacks,
      operandBoundaryBase, copyAccumulatorResultBase]
  rw [hs]

theorem fullCopyAccumulator_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    ((fun o => o.bind (TM2.step (fullCopyProgram returnLabel right)))^[2 * w + 3])
      (some (lensRenamedCfg
        (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
          (by decide))
        FullInterpreterState.moveLens
        (copyCfg .scan ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        state (operandBoundaryBase w accumulator m base))) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.moveLens.put state default)
        (copyAccumulatorResultBase w accumulator m base))) := by
  have h := run_lensPhase_to_right
    (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
      (by decide))
    FullInterpreterState.moveLens copyProgram .done (by rfl) returnLabel right
    (copy_correct ((fixedBits w accumulator).map SparseSymbol.bit) []) rfl
    state (operandBoundaryBase w accumulator m base)
  simp only [List.length_map, fixedBits_length] at h
  simp only [List.append_nil] at h
  rw [fullCopy_return_bridge returnLabel w accumulator m base state] at h
  simpa [fullCopyProgram] using h

end Lax51Proofs.RamToTM
