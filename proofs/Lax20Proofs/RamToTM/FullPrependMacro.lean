import Lax20Proofs.RamToTM.FullCopyMacro

namespace Lax20Proofs.RamToTM

open Turing TM2

abbrev FullPrependLabel (R : Type) := Sum PrependCellLabel R

def fullPrependProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullPrependLabel R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (FullPrependLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft prependCoreRenaming FullInterpreterState.prependLens
      prependCoreProgram .done returnLabel)
    right

def prependResultStacks (w a v : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .work0 | .work1 => []
  | .memory => encodeSparseMemory w (m.write w a v) ++ [.memoryEnd]
  | k => base k

theorem encodeSparseMemory_write (w : Nat) (m : SparseMemory) (a v : Nat) :
    encodeSparseMemory w (m.write w a v) =
      encodeSparseCell w (a, v) ++ encodeSparseMemory w m := by
  simp [SparseMemory.write, encodeSparseMemory]
  simp [encodeSparseCell, encodeFixedWord, fixedBits_mod_word]

theorem fullPrepend_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w a v : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg prependCoreRenaming FullInterpreterState.prependLens
      returnLabel
      (prependLocalCfg .done [] []
        (encodeSparseCell w (a, v) ++ (encodeSparseMemory w m ++ [.memoryEnd])))
      state
      (fun
        | .work0 => (fixedBits w a).reverse.map SparseSymbol.bit
        | .work1 => (fixedBits w v).reverse.map SparseSymbol.bit
        | .memory => encodeSparseMemory w m ++ [.memoryEnd]
        | k => base k) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.prependLens.put state default)
      (prependResultStacks w a v m base) := by
  simp only [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg, prependLocalCfg]
  have hs : renamedStacks prependCoreRenaming
      (prependCellStacks [] []
        (encodeSparseCell w (a, v) ++ (encodeSparseMemory w m ++ [.memoryEnd])))
      (fun
        | .work0 => (fixedBits w a).reverse.map SparseSymbol.bit
        | .work1 => (fixedBits w v).reverse.map SparseSymbol.bit
        | .memory => encodeSparseMemory w m ++ [.memoryEnd]
        | k => base k) = prependResultStacks w a v m base := by
    funext k
    cases k <;> simp [renamedStacks, prependCoreRenaming, prependCoreDecode,
      prependCoreEncode, prependCellStacks, prependResultStacks,
      encodeSparseMemory_write, List.append_assoc]
  rw [hs]

theorem fullPrepend_fixed_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a v : Nat) (m : SparseMemory)
    (base : CoreStack -> List SparseSymbol)
    (state : FullInterpreterState N) :
    let initialStacks : CoreStack -> List SparseSymbol := fun
      | .work0 => (fixedBits w a).reverse.map SparseSymbol.bit
      | .work1 => (fixedBits w v).reverse.map SparseSymbol.bit
      | .memory => encodeSparseMemory w m ++ [.memoryEnd]
      | k => base k
    ((fun o => o.bind (TM2.step (fullPrependProgram returnLabel right)))^[
      2 * w + 6])
      (some (lensRenamedCfg prependCoreRenaming
        FullInterpreterState.prependLens
        (prependLocalCfg .cellEnd
          ((fixedBits w a).reverse.map SparseSymbol.bit)
          ((fixedBits w v).reverse.map SparseSymbol.bit)
          (encodeSparseMemory w m ++ [.memoryEnd])) state initialStacks)) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.prependLens.put state default)
        (prependResultStacks w a v m base))) := by
  dsimp only
  let initialStacks : CoreStack -> List SparseSymbol := fun
    | .work0 => (fixedBits w a).reverse.map SparseSymbol.bit
    | .work1 => (fixedBits w v).reverse.map SparseSymbol.bit
    | .memory => encodeSparseMemory w m ++ [.memoryEnd]
    | k => base k
  have h := run_lensPhase_to_right prependCoreRenaming
    FullInterpreterState.prependLens prependCoreProgram .done (by rfl)
    returnLabel right
    (prependLocal_fixed_correct w a v
      (encodeSparseMemory w m ++ [.memoryEnd])) rfl state initialStacks
  dsimp [initialStacks] at h
  rw [fullPrepend_return_bridge returnLabel w a v m base state] at h
  simpa [fullPrependProgram, initialStacks] using h

end Lax20Proofs.RamToTM
