import Lax20Proofs.RamToTM.RestoreComparedOperands

namespace Lax20Proofs.RamToTM

open Turing TM2

theorem sparseSubLocal_fixed_run (w a b : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    ((fun o => o.bind (TM2.step sparseSubCoreProgram))^[w + 1])
      (some (sparseSubLocalCfg false (fixedBits w a) (fixedBits w b) [])) =
    some (sparseSubLocalDoneCfg (decide (a < b))
      (subBits (fixedBits w a) (fixedBits w b) false).reverse) := by
  have hp : sparseSubCoreProgram = sparseSubProgram := by
    funext l
    cases l <;> rfl
  rw [hp]
  have hrun := subMachine_reaches_done false
    (fixedBits w a) (fixedBits w b) [] (by simp)
  rw [subBorrowOut_fixed_eq_decide_lt w a b ha hb] at hrun
  have hsparse := transport_iterate_mapAlphabetProgram
    sparseBitEncode sparseBitDecode sparseBitDecode_encode subMachine.m hrun
  simpa [sparseSubLocalCfg, sparseSubLocalDoneCfg, sparseSubCfg,
    sparseSubDoneCfg, subCfg, subDoneCfg, subPartialDoneCfg,
    mapAlphabetCfg] using hsparse

abbrev FullSubtractCoreLabel (R : Type) := Sum AddLabel R

def fullSubtractCoreProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullSubtractCoreLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullSubtractCoreLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft binaryCoreRenaming FullInterpreterState.subLens
      sparseSubCoreProgram .done returnLabel)
    right

def subtractCoreResultStacks (w a b : Nat)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .accumulator | .work1 => []
  | .work0 =>
      (subBits (fixedBits w a) (fixedBits w b) false).reverse.map SparseSymbol.bit
  | k => base k

theorem fullSubtractCore_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w a b : Nat)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg binaryCoreRenaming FullInterpreterState.subLens returnLabel
      (sparseSubLocalDoneCfg (decide (a < b))
        (subBits (fixedBits w a) (fixedBits w b) false).reverse)
      state base =
    cleanReturnCfg returnLabel
      (FullInterpreterState.subLens.put state
        ⟨decide (a < b), none, none⟩)
      (subtractCoreResultStacks w a b base) := by
  simp only [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    sparseSubLocalDoneCfg]
  have hs : renamedStacks binaryCoreRenaming
      (mapAlphabetStacks sparseBitEncode
        (addStackFamily [] []
          (subBits (fixedBits w a) (fixedBits w b) false).reverse))
      base = subtractCoreResultStacks w a b base := by
    funext k
    cases k <;> simp [renamedStacks, binaryCoreRenaming, binaryCoreDecode,
      addStackFamily, mapAlphabetStacks, sparseBitEncode,
      subtractCoreResultStacks]
  rw [hs]

theorem fullSubtractCore_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b : Nat) (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    ((fun o => o.bind (TM2.step
      (fullSubtractCoreProgram returnLabel right)))^[w + 2])
      (some (lensRenamedCfg binaryCoreRenaming FullInterpreterState.subLens
        (sparseSubLocalCfg false (fixedBits w a) (fixedBits w b) [])
        state base)) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.subLens.put state
          ⟨decide (a < b), none, none⟩)
        (subtractCoreResultStacks w a b base))) := by
  have h := run_lensPhase_to_right binaryCoreRenaming
    FullInterpreterState.subLens sparseSubCoreProgram .done (by rfl)
    returnLabel right (sparseSubLocal_fixed_run w a b ha hb) rfl state base
  rw [fullSubtractCore_return_bridge returnLabel w a b base state] at h
  simpa [fullSubtractCoreProgram] using h

end Lax20Proofs.RamToTM
