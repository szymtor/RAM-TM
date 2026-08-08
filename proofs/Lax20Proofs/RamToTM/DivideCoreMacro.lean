import Lax20Proofs.RamToTM.MultiplyCoreMacro

namespace Lax20Proofs.RamToTM

open Turing TM2

def divBaseProgram : DivLabel →
    TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl :=
  fun label => divMachine.m label

def sparseDivCoreProgram : DivLabel →
    TM2.Stmt (fun _ : DivStack => SparseSymbol) DivLabel DivControl :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode divBaseProgram

def sparseDivLocalInitialCfg (dividend divisor remainder : List Bool) :
    TM2.Cfg (fun _ : DivStack => SparseSymbol) DivLabel DivControl where
  l := some .inspectDivisor
  var := default
  stk := mapAlphabetStacks sparseBitEncode
    (divStacks dividend divisor remainder [] [] [] [] [])

def sparseDivLocalDoneCfg (divisorNonzero : Bool)
    (divisor remainder quotient : List Bool) :
    TM2.Cfg (fun _ : DivStack => SparseSymbol) DivLabel DivControl where
  l := some .done
  var := { (default : DivControl) with divisorNonzero := divisorNonzero }
  stk := mapAlphabetStacks sparseBitEncode
    (divStacks [] divisor remainder quotient [] [] [] [])

theorem sparseDivLocal_zero_correct (w a : ℕ) :
    ((fun o => o.bind (TM2.step sparseDivCoreProgram))^[divZeroRunTime w])
      (some (sparseDivLocalInitialCfg (fixedBits w a).reverse
        (fixedBits (w + 1) 0) (fixedBits (w + 1) 0))) =
      some (sparseDivLocalDoneCfg false (fixedBits (w + 1) 0)
        (fixedBits (w + 1) 0) (fixedBits w 0)) := by
  have hp : sparseDivCoreProgram = sparseDivProgram := by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseDivLocalInitialCfg, sparseDivLocalDoneCfg, sparseDivInitialCfg,
    sparseDivDoneCfg, divInitialCfg, divDoneCfg, divCfg, mapAlphabetCfg] using
      sparseDiv_zero_correct w a

theorem sparseDivLocal_positive_correct (w a d : ℕ)
    (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w) :
    ((fun o => o.bind (TM2.step sparseDivCoreProgram))^[divPositiveRunTime w])
      (some (sparseDivLocalInitialCfg (fixedBits w a).reverse
        (fixedBits (w + 1) d) (fixedBits (w + 1) 0))) =
      some (sparseDivLocalDoneCfg true (fixedBits (w + 1) d)
        (fixedBits (w + 1) (a % d)) (fixedBits w (a / d))) := by
  have hp : sparseDivCoreProgram = sparseDivProgram := by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseDivLocalInitialCfg, sparseDivLocalDoneCfg, sparseDivInitialCfg,
    sparseDivDoneCfg, divInitialCfg, divDoneCfg, divCfg, mapAlphabetCfg] using
      sparseDiv_positive_correct w a d ha hd0 hd

theorem sparseDiv_core_zero_correct {Λx τ : Type} (w a : ℕ)
    (returnLabel : Λx)
    (ambientProgram : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum DivLabel Λx) (DivControl × τ))
    (ambientState : τ) (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (renamedSpliceProgram divCoreRenaming
      sparseDivCoreProgram .done returnLabel ambientProgram)))^[divZeroRunTime w + 1])
      (some (renamedCfg divCoreRenaming
        (sparseDivLocalInitialCfg (fixedBits w a).reverse
          (fixedBits (w + 1) 0) (fixedBits (w + 1) 0))
        ambientState ambientStacks)) =
      some (renamedReturnCfg divCoreRenaming returnLabel
        (sparseDivLocalDoneCfg false (fixedBits (w + 1) 0)
          (fixedBits (w + 1) 0) (fixedBits w 0))
        ambientState ambientStacks) := by
  exact transport_renamedHaltingMacro_and_return divCoreRenaming
    sparseDivCoreProgram .done (by rfl) returnLabel ambientProgram
    (sparseDivLocal_zero_correct w a) rfl ambientState ambientStacks

theorem sparseDiv_core_positive_correct {Λx τ : Type} (w a d : ℕ)
    (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w)
    (returnLabel : Λx)
    (ambientProgram : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum DivLabel Λx) (DivControl × τ))
    (ambientState : τ) (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (renamedSpliceProgram divCoreRenaming
      sparseDivCoreProgram .done returnLabel ambientProgram)))^[divPositiveRunTime w + 1])
      (some (renamedCfg divCoreRenaming
        (sparseDivLocalInitialCfg (fixedBits w a).reverse
          (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
        ambientState ambientStacks)) =
      some (renamedReturnCfg divCoreRenaming returnLabel
        (sparseDivLocalDoneCfg true (fixedBits (w + 1) d)
          (fixedBits (w + 1) (a % d)) (fixedBits w (a / d)))
        ambientState ambientStacks) := by
  exact transport_renamedHaltingMacro_and_return divCoreRenaming
    sparseDivCoreProgram .done (by rfl) returnLabel ambientProgram
    (sparseDivLocal_positive_correct w a d ha hd0 hd) rfl
    ambientState ambientStacks

end Lax20Proofs.RamToTM
