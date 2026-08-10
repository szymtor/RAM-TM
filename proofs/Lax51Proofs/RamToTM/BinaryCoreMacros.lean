import Lax51Proofs.RamToTM.ArithmeticStackRenamings

namespace Lax51Proofs.RamToTM

open Turing TM2

def sparseAddCoreProgram : AddLabel →
    TM2.Stmt (fun _ : AddStack => SparseSymbol) AddLabel AddControl
  | .loop => mapAlphabetStmt sparseBitEncode sparseBitDecode
      (addIteration .left .right .result .loop .done)
  | .done => .halt

def sparseAddLocalCfg (carry : Bool) (left right result : List Bool) :
    TM2.Cfg (fun _ : AddStack => SparseSymbol) AddLabel AddControl where
  l := some .loop
  var := ⟨carry, none, none⟩
  stk := mapAlphabetStacks sparseBitEncode (addStackFamily left right result)

def sparseAddLocalDoneCfg (carry : Bool) (right result : List Bool) :
    TM2.Cfg (fun _ : AddStack => SparseSymbol) AddLabel AddControl where
  l := some .done
  var := ⟨carry, none, none⟩
  stk := mapAlphabetStacks sparseBitEncode (addStackFamily [] right result)

theorem sparseAddLocal_correct (carry : Bool) (left right result : List Bool)
    (hlen : left.length = right.length) :
    ((fun o => o.bind (TM2.step sparseAddCoreProgram))^[left.length + 1])
      (some (sparseAddLocalCfg carry left right result)) =
      some (sparseAddLocalDoneCfg (addCarryOut left right carry) []
        ((addBits left right carry).reverse ++ result)) := by
  have hp : sparseAddCoreProgram = sparseAddProgram := by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseAddLocalCfg, sparseAddLocalDoneCfg, sparseAddCfg,
    sparseAddDoneCfg, addCfg, addDoneCfg, mapAlphabetCfg] using
      sparseAdd_reaches_done carry left right result hlen

def sparseZipCoreProgram (f : Bool → Bool → Bool) : AddLabel →
    TM2.Stmt (fun _ : AddStack => SparseSymbol) AddLabel ZipControl
  | .loop => mapAlphabetStmt sparseBitEncode sparseBitDecode
      (zipIteration f .left .right .result .loop .done)
  | .done => .halt

def sparseZipLocalCfg (f : Bool → Bool → Bool)
    (left right result : List Bool) :
    TM2.Cfg (fun _ : AddStack => SparseSymbol) AddLabel ZipControl where
  l := some .loop
  var := ⟨none, none⟩
  stk := mapAlphabetStacks sparseBitEncode (addStackFamily left right result)

def sparseZipLocalDoneCfg (f : Bool → Bool → Bool) (result : List Bool) :
    TM2.Cfg (fun _ : AddStack => SparseSymbol) AddLabel ZipControl where
  l := some .done
  var := ⟨none, none⟩
  stk := mapAlphabetStacks sparseBitEncode (addStackFamily [] [] result)

theorem sparseZipLocal_correct (f : Bool → Bool → Bool)
    (left right result : List Bool) (hlen : left.length = right.length) :
    ((fun o => o.bind (TM2.step (sparseZipCoreProgram f)))^[left.length + 1])
      (some (sparseZipLocalCfg f left right result)) =
      some (sparseZipLocalDoneCfg f ((zipBits f left right).reverse ++ result)) := by
  have hp : sparseZipCoreProgram f = sparseZipProgram f := by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseZipLocalCfg, sparseZipLocalDoneCfg, sparseZipCfg,
    sparseZipDoneCfg, zipCfg, zipDoneCfg, zipPartialDoneCfg,
    mapAlphabetCfg] using
      sparseZip_reaches_done f left right result hlen

def sparseSubCoreProgram : AddLabel →
    TM2.Stmt (fun _ : AddStack => SparseSymbol) AddLabel SubControl
  | .loop => mapAlphabetStmt sparseBitEncode sparseBitDecode
      (subIteration .left .right .result .loop .done)
  | .done => .halt

def sparseSubLocalCfg (borrow : Bool) (left right result : List Bool) :
    TM2.Cfg (fun _ : AddStack => SparseSymbol) AddLabel SubControl where
  l := some .loop
  var := ⟨borrow, none, none⟩
  stk := mapAlphabetStacks sparseBitEncode (addStackFamily left right result)

def sparseSubLocalDoneCfg (borrow : Bool) (result : List Bool) :
    TM2.Cfg (fun _ : AddStack => SparseSymbol) AddLabel SubControl where
  l := some .done
  var := ⟨borrow, none, none⟩
  stk := mapAlphabetStacks sparseBitEncode (addStackFamily [] [] result)

theorem sparseSubLocal_fixed_correct (w : ℕ) {a b : ℕ}
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hba : b ≤ a) :
    ((fun o => o.bind (TM2.step sparseSubCoreProgram))^[w + 1])
      (some (sparseSubLocalCfg false (fixedBits w a) (fixedBits w b) [])) =
      some (sparseSubLocalDoneCfg false (fixedBits w (a - b)).reverse) := by
  have hp : sparseSubCoreProgram = sparseSubProgram := by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseSubLocalCfg, sparseSubLocalDoneCfg, sparseSubCfg,
    sparseSubDoneCfg, subCfg, subDoneCfg, subPartialDoneCfg,
    mapAlphabetCfg] using sparseSub_fixed_correct w ha hb hba

theorem sparseAdd_core_correct {Λx τ : Type}
    (carry : Bool) (left rightBits result : List Bool)
    (hlen : left.length = rightBits.length) (returnLabel : Λx)
    (ambientProgram : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum AddLabel Λx) (AddControl × τ))
    (ambientState : τ) (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (renamedSpliceProgram binaryCoreRenaming
      sparseAddCoreProgram .done returnLabel ambientProgram)))^[left.length + 2])
      (some (renamedCfg binaryCoreRenaming
        (sparseAddLocalCfg carry left rightBits result)
        ambientState ambientStacks)) =
      some (renamedReturnCfg binaryCoreRenaming returnLabel
        (sparseAddLocalDoneCfg (addCarryOut left rightBits carry) []
          ((addBits left rightBits carry).reverse ++ result))
        ambientState ambientStacks) := by
  convert transport_renamedHaltingMacro_and_return binaryCoreRenaming
    sparseAddCoreProgram .done (by rfl) returnLabel ambientProgram
    (sparseAddLocal_correct carry left rightBits result hlen) rfl
    ambientState ambientStacks using 1 <;> omega

theorem sparseZip_core_correct {Λx τ : Type} (f : Bool → Bool → Bool)
    (left rightBits result : List Bool) (hlen : left.length = rightBits.length)
    (returnLabel : Λx)
    (ambientProgram : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum AddLabel Λx) (ZipControl × τ))
    (ambientState : τ) (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (renamedSpliceProgram binaryCoreRenaming
      (sparseZipCoreProgram f) .done returnLabel ambientProgram)))^[left.length + 2])
      (some (renamedCfg binaryCoreRenaming
        (sparseZipLocalCfg f left rightBits result)
        ambientState ambientStacks)) =
      some (renamedReturnCfg binaryCoreRenaming returnLabel
        (sparseZipLocalDoneCfg f ((zipBits f left rightBits).reverse ++ result))
        ambientState ambientStacks) := by
  convert transport_renamedHaltingMacro_and_return binaryCoreRenaming
    (sparseZipCoreProgram f) .done (by rfl) returnLabel ambientProgram
    (sparseZipLocal_correct f left rightBits result hlen) rfl
    ambientState ambientStacks using 1 <;> omega

theorem sparseSub_core_fixed_correct {Λx τ : Type} (w : ℕ) {a b : ℕ}
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hba : b ≤ a)
    (returnLabel : Λx)
    (ambientProgram : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum AddLabel Λx) (SubControl × τ))
    (ambientState : τ) (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (renamedSpliceProgram binaryCoreRenaming
      sparseSubCoreProgram .done returnLabel ambientProgram)))^[w + 2])
      (some (renamedCfg binaryCoreRenaming
        (sparseSubLocalCfg false (fixedBits w a) (fixedBits w b) [])
        ambientState ambientStacks)) =
      some (renamedReturnCfg binaryCoreRenaming returnLabel
        (sparseSubLocalDoneCfg false (fixedBits w (a - b)).reverse)
        ambientState ambientStacks) := by
  convert transport_renamedHaltingMacro_and_return binaryCoreRenaming
    sparseSubCoreProgram .done (by rfl) returnLabel ambientProgram
    (sparseSubLocal_fixed_correct w ha hb hba) rfl
    ambientState ambientStacks using 1 <;> omega

end Lax51Proofs.RamToTM
