import Lax51Proofs.RamToTM.FullInterpreterState
import Lax51Proofs.RamToTM.PhaseComposition

namespace Lax51Proofs.RamToTM

open Turing TM2

theorem fullLookup_found {N : ℕ} {R : Type}
    (w query value : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hfind : m.find? query = some value) (processed : List SparseSymbol)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum LookupScanLabel R) (FullInterpreterState N))
    (ambientState : FullInterpreterState N)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ∃ steps ≤ m.length * (12 * w + 22) + 11 * w +
        processed.length + 22,
      ((fun o => o.bind (TM2.step (lensSpliceProgram lookupCoreRenaming
        FullInterpreterState.lookupLens lookupScanProgram
        .found returnLabel right)))^[steps + 1])
        (some (lensRenamedCfg lookupCoreRenaming
          FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] []
            processed [])
          ambientState ambientStacks)) =
      some (lensReturnCfg lookupCoreRenaming FullInterpreterState.lookupLens
        returnLabel
        (lookupScanMacroCfg .found true
          (processed.reverse ++ encodeSparseMemory w m ++ [.memoryEnd]) []
          ((fixedBits w value).reverse.map SparseSymbol.bit) []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        ambientState ambientStacks) := by
  rcases lookupScan_found w query value hq m hm hfind processed with
    ⟨steps, hbound, hrun⟩
  refine ⟨steps, hbound, ?_⟩
  apply transport_lensHaltingMacro_and_return lookupCoreRenaming
    FullInterpreterState.lookupLens lookupScanProgram .found (by rfl)
    returnLabel right
  · simpa [lookupScanProgram, lookupScanMacroCfg, lookupScanCfg,
      lookupScanMachine] using hrun
  · rfl

theorem fullLookup_missing {N : ℕ} {R : Type}
    (w query : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? query = none) (processed : List SparseSymbol)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum LookupScanLabel R) (FullInterpreterState N))
    (ambientState : FullInterpreterState N)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram lookupCoreRenaming
      FullInterpreterState.lookupLens lookupScanProgram
      .missing returnLabel right)))^[
        m.length * (12 * w + 22) + processed.length + 3])
      (some (lensRenamedCfg lookupCoreRenaming
        FullInterpreterState.lookupLens
        (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] []
          processed [])
        ambientState ambientStacks)) =
    some (lensReturnCfg lookupCoreRenaming FullInterpreterState.lookupLens
      returnLabel
      (lookupScanMacroCfg .missing (decide m.isEmpty)
        (processed.reverse ++ encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
      ambientState ambientStacks) := by
  have hrun :
      ((fun o : Option
          (TM2.Cfg (fun _ : LookupScanStack => SparseSymbol)
            LookupScanLabel LookupCellControl) =>
        o.bind (TM2.step lookupScanProgram))^[
          m.length * (12 * w + 22) + processed.length + 2])
        (some (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] []
          processed [])) =
      some (lookupScanMacroCfg .missing (decide m.isEmpty)
        (processed.reverse ++ encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] []) := by
    simpa [lookupScanProgram, lookupScanMacroCfg, lookupScanCfg,
      lookupScanMachine] using
      lookupScan_all_missing w query hq m hm hmissing true processed
  convert transport_lensHaltingMacro_and_return lookupCoreRenaming
    FullInterpreterState.lookupLens lookupScanProgram .missing (by rfl)
    returnLabel right hrun rfl ambientState ambientStacks using 1 <;> omega

end Lax51Proofs.RamToTM
