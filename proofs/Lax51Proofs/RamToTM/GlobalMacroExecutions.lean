import Lax51Proofs.RamToTM.InterpreterMacroState

namespace Lax51Proofs.RamToTM

open Turing TM2

theorem globalAdd_correct {Λx : Type} (carry : Bool)
    (left rightBits result : List Bool) (hlen : left.length = rightBits.length)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum AddLabel Λx) InterpreterMacroState)
    (ambientState : InterpreterMacroState)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram binaryCoreRenaming
      InterpreterMacroState.addLens sparseAddCoreProgram .done returnLabel right)))^[
        left.length + 2])
      (some (lensRenamedCfg binaryCoreRenaming InterpreterMacroState.addLens
        (sparseAddLocalCfg carry left rightBits result)
        ambientState ambientStacks)) =
      some (lensReturnCfg binaryCoreRenaming InterpreterMacroState.addLens returnLabel
        (sparseAddLocalDoneCfg (addCarryOut left rightBits carry) []
          ((addBits left rightBits carry).reverse ++ result))
        ambientState ambientStacks) := by
  convert transport_lensHaltingMacro_and_return binaryCoreRenaming
    InterpreterMacroState.addLens sparseAddCoreProgram .done (by rfl)
    returnLabel right (sparseAddLocal_correct carry left rightBits result hlen) rfl
    ambientState ambientStacks using 1 <;> omega

theorem globalZip_correct {Λx : Type} (f : Bool → Bool → Bool)
    (left rightBits result : List Bool) (hlen : left.length = rightBits.length)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum AddLabel Λx) InterpreterMacroState)
    (ambientState : InterpreterMacroState)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram binaryCoreRenaming
      InterpreterMacroState.zipLens (sparseZipCoreProgram f) .done returnLabel right)))^[
        left.length + 2])
      (some (lensRenamedCfg binaryCoreRenaming InterpreterMacroState.zipLens
        (sparseZipLocalCfg f left rightBits result) ambientState ambientStacks)) =
      some (lensReturnCfg binaryCoreRenaming InterpreterMacroState.zipLens returnLabel
        (sparseZipLocalDoneCfg f ((zipBits f left rightBits).reverse ++ result))
        ambientState ambientStacks) := by
  convert transport_lensHaltingMacro_and_return binaryCoreRenaming
    InterpreterMacroState.zipLens (sparseZipCoreProgram f) .done (by rfl)
    returnLabel right (sparseZipLocal_correct f left rightBits result hlen) rfl
    ambientState ambientStacks using 1 <;> omega

theorem globalMul_fixed_correct {Λx : Type} (w a b : ℕ)
    (hw : 0 < w) (hb : b < 2 ^ w) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum MulLabel Λx) InterpreterMacroState)
    (ambientState : InterpreterMacroState)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ∃ finalMultiplicand : List Bool,
      ((fun o => o.bind (TM2.step (lensSpliceProgram mulCoreRenaming
        InterpreterMacroState.mulLens sparseMulCoreProgram .done returnLabel right)))^[
          mulRunTime (fixedBits w b) w + 1])
        (some (lensRenamedCfg mulCoreRenaming InterpreterMacroState.mulLens
          (sparseMulLocalOuterCfg
            (fixedBits w b) (fixedBits w a) (fixedBits w 0))
          ambientState ambientStacks)) =
      some (lensReturnCfg mulCoreRenaming InterpreterMacroState.mulLens returnLabel
        (sparseMulLocalDoneCfg finalMultiplicand (fixedBits w (a * b)))
        ambientState ambientStacks) := by
  rcases sparseMulLocal_fixed_correct w a b hw hb with ⟨final, hrun⟩
  refine ⟨final, ?_⟩
  exact transport_lensHaltingMacro_and_return mulCoreRenaming
    InterpreterMacroState.mulLens sparseMulCoreProgram .done (by rfl)
    returnLabel right hrun rfl ambientState ambientStacks

theorem globalDiv_positive_correct {Λx : Type} (w a d : ℕ)
    (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum DivLabel Λx) InterpreterMacroState)
    (ambientState : InterpreterMacroState)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram divCoreRenaming
      InterpreterMacroState.divLens sparseDivCoreProgram .done returnLabel right)))^[
        divPositiveRunTime w + 1])
      (some (lensRenamedCfg divCoreRenaming InterpreterMacroState.divLens
        (sparseDivLocalInitialCfg (fixedBits w a).reverse
          (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
        ambientState ambientStacks)) =
      some (lensReturnCfg divCoreRenaming InterpreterMacroState.divLens returnLabel
        (sparseDivLocalDoneCfg true (fixedBits (w + 1) d)
          (fixedBits (w + 1) (a % d)) (fixedBits w (a / d)))
        ambientState ambientStacks) := by
  exact transport_lensHaltingMacro_and_return divCoreRenaming
    InterpreterMacroState.divLens sparseDivCoreProgram .done (by rfl)
    returnLabel right (sparseDivLocal_positive_correct w a d ha hd0 hd) rfl
    ambientState ambientStacks

theorem globalMove_correct {Λx : Type}
    (sourceStack targetStack : CoreStack) (hne : sourceStack ≠ targetStack)
    (source target : List SparseSymbol) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum SymbolMoveLabel Λx) InterpreterMacroState)
    (ambientState : InterpreterMacroState)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram
      (symbolMoveCoreRenaming sourceStack targetStack hne)
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done returnLabel right)))^[
        source.length + 2])
      (some (lensRenamedCfg (symbolMoveCoreRenaming sourceStack targetStack hne)
        InterpreterMacroState.moveLens (symbolMoveLocalCfg .loop source target)
        ambientState ambientStacks)) =
      some (lensReturnCfg (symbolMoveCoreRenaming sourceStack targetStack hne)
        InterpreterMacroState.moveLens returnLabel
        (symbolMoveLocalCfg .done [] (source.reverse ++ target))
        ambientState ambientStacks) := by
  convert transport_lensHaltingMacro_and_return
    (symbolMoveCoreRenaming sourceStack targetStack hne)
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel right (symbolMoveLocal_correct source target) rfl
    ambientState ambientStacks using 1 <;> omega

theorem globalZero_fixed_correct {Λx : Type} (w query : ℕ)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum ZeroWordLabel Λx) InterpreterMacroState)
    (ambientState : InterpreterMacroState)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram zeroWordCoreRenaming
      InterpreterMacroState.zeroLens zeroWordProgram .done returnLabel right)))^[
        2 * w + 3])
      (some (lensRenamedCfg zeroWordCoreRenaming
        InterpreterMacroState.zeroLens
        (zeroWordTypedCfg .fill
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [])
        ambientState ambientStacks)) =
      some (lensReturnCfg zeroWordCoreRenaming InterpreterMacroState.zeroLens
        returnLabel
        (zeroWordTypedCfg .done
          ((fixedBits w query).reverse.map SparseSymbol.bit) []
          ((fixedBits w 0).reverse.map SparseSymbol.bit))
        ambientState ambientStacks) := by
  convert transport_lensHaltingMacro_and_return zeroWordCoreRenaming
    InterpreterMacroState.zeroLens zeroWordProgram .done (by rfl)
    returnLabel right (zeroWordTyped_fixed_correct w query) rfl
    ambientState ambientStacks using 1 <;> omega

theorem globalZero_correct {Λx : Type} (query result : List SparseSymbol)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum ZeroWordLabel Λx) InterpreterMacroState)
    (ambientState : InterpreterMacroState)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram zeroWordCoreRenaming
      InterpreterMacroState.zeroLens zeroWordProgram .done returnLabel right)))^[
        2 * query.length + 3])
      (some (lensRenamedCfg zeroWordCoreRenaming
        InterpreterMacroState.zeroLens
        (zeroWordTypedCfg .fill query [] result)
        ambientState ambientStacks)) =
      some (lensReturnCfg zeroWordCoreRenaming InterpreterMacroState.zeroLens
        returnLabel
        (zeroWordTypedCfg .done query []
          (List.replicate query.length (.bit false) ++ result))
        ambientState ambientStacks) := by
  convert transport_lensHaltingMacro_and_return zeroWordCoreRenaming
    InterpreterMacroState.zeroLens zeroWordProgram .done (by rfl)
    returnLabel right (zeroWordTyped_correct query result) rfl
    ambientState ambientStacks using 1 <;> omega

theorem globalPrepend_fixed_correct {Λx : Type}
    (w a v : ℕ) (memory : List SparseSymbol) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum PrependCellLabel Λx) InterpreterMacroState)
    (ambientState : InterpreterMacroState)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram prependCoreRenaming
      InterpreterMacroState.prependLens prependCoreProgram .done returnLabel right)))^[
        2 * w + 6])
      (some (lensRenamedCfg prependCoreRenaming InterpreterMacroState.prependLens
        (prependLocalCfg .cellEnd
          ((fixedBits w a).reverse.map SparseSymbol.bit)
          ((fixedBits w v).reverse.map SparseSymbol.bit) memory)
        ambientState ambientStacks)) =
      some (lensReturnCfg prependCoreRenaming InterpreterMacroState.prependLens
        returnLabel (prependLocalCfg .done [] [] (encodeSparseCell w (a, v) ++ memory))
        ambientState ambientStacks) := by
  convert transport_lensHaltingMacro_and_return prependCoreRenaming
    InterpreterMacroState.prependLens prependCoreProgram .done (by rfl)
    returnLabel right (prependLocal_fixed_correct w a v memory) rfl
    ambientState ambientStacks using 1 <;> omega

theorem globalLookup_found {Λx : Type}
    (w query value : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hfind : m.find? query = some value) (processed : List SparseSymbol)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum LookupScanLabel Λx) InterpreterMacroState)
    (ambientState : InterpreterMacroState)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ∃ steps ≤ m.length * (12 * w + 22) + 11 * w + processed.length + 22,
      ((fun o => o.bind (TM2.step (lensSpliceProgram lookupCoreRenaming
        InterpreterMacroState.lookupLens lookupScanProgram .found returnLabel right)))^[
          steps + 1])
        (some (lensRenamedCfg lookupCoreRenaming InterpreterMacroState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])
          ambientState ambientStacks)) =
        some (lensReturnCfg lookupCoreRenaming InterpreterMacroState.lookupLens
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
    InterpreterMacroState.lookupLens lookupScanProgram .found (by rfl)
    returnLabel right
  · simpa [lookupScanProgram, lookupScanMacroCfg, lookupScanCfg,
      lookupScanMachine] using hrun
  · rfl

theorem globalLookup_missing {Λx : Type}
    (w query : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? query = none) (equal : Bool)
    (processed : List SparseSymbol) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum LookupScanLabel Λx) InterpreterMacroState)
    (ambientState : InterpreterMacroState)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram lookupCoreRenaming
      InterpreterMacroState.lookupLens lookupScanProgram .missing returnLabel right)))^[
        m.length * (12 * w + 22) + processed.length + 3])
      (some (lensRenamedCfg lookupCoreRenaming InterpreterMacroState.lookupLens
        (lookupScanMacroCfg .scan equal
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])
        ambientState ambientStacks)) =
      some (lensReturnCfg lookupCoreRenaming InterpreterMacroState.lookupLens
        returnLabel
        (lookupScanMacroCfg .missing (equal && decide m.isEmpty)
          (processed.reverse ++ encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        ambientState ambientStacks) := by
  have hrun :
      ((fun o : Option
          (TM2.Cfg (fun _ : LookupScanStack => SparseSymbol)
            LookupScanLabel LookupCellControl) =>
        o.bind (TM2.step lookupScanProgram))^[
          m.length * (12 * w + 22) + processed.length + 2])
        (some (lookupScanMacroCfg .scan equal
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])) =
        some (lookupScanMacroCfg .missing (equal && decide m.isEmpty)
          (processed.reverse ++ encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] []) := by
    simpa [lookupScanProgram, lookupScanMacroCfg, lookupScanCfg,
      lookupScanMachine] using
      lookupScan_all_missing w query hq m hm hmissing equal processed
  convert transport_lensHaltingMacro_and_return lookupCoreRenaming
    InterpreterMacroState.lookupLens lookupScanProgram .missing (by rfl)
    returnLabel right hrun rfl ambientState ambientStacks using 1 <;> omega

end Lax51Proofs.RamToTM
