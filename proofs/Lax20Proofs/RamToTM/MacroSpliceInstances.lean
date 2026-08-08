import Lax20Proofs.RamToTM.MacroSplice

namespace Lax20Proofs.RamToTM

open Turing TM2

/-! Ready-to-use spliced forms of the two macros used by operand evaluation. -/

def literalWordProgram (n : ℕ) : LiteralWordLabel →
    TM2.Stmt (fun _ : LiteralWordStack => SparseSymbol) LiteralWordLabel
      (LiteralWordControl n) :=
  (literalWordMachine n).m

def lookupScanProgram : LookupScanLabel →
    TM2.Stmt (fun _ : LookupScanStack => SparseSymbol) LookupScanLabel
      LookupCellControl :=
  lookupScanMachine.m

def literalWordMacroCfg (n : ℕ) (label : LiteralWordLabel)
    (remaining : Fin (n + 1)) (query backup result : List SparseSymbol) :
    TM2.Cfg (fun _ : LiteralWordStack => SparseSymbol) LiteralWordLabel
      (LiteralWordControl n) where
  l := some label
  var := ⟨none, remaining⟩
  stk := literalWordStacks query backup result

def lookupScanMacroCfg (label : LookupScanLabel) (equal : Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash :
      List SparseSymbol) :
    TM2.Cfg (fun _ : LookupScanStack => SparseSymbol) LookupScanLabel
      LookupCellControl where
  l := some label
  var := ⟨none, equal, none, none⟩
  stk := lookupScanStacks source address value cellBackup query addressBackup queryBackup
    processed trash

theorem literalWord_spliced_correct {Kx Λx τ : Type}
    [DecidableEq (Sum LiteralWordStack Kx)]
    (n : ℕ) (query result : List SparseSymbol) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum LiteralWordStack Kx => SparseSymbol)
      (Sum LiteralWordLabel Λx) (LiteralWordControl n × τ))
    (ambient : τ) (rightStacks : Kx → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (spliceLeftProgram (literalWordProgram n)
      .done returnLabel right)))^[2 * query.length + 2 + 1])
      (some (embedLeftCfg
        (literalWordMacroCfg n .emit ⟨n, Nat.lt_succ_self n⟩ query [] result)
        ambient rightStacks)) =
      some (spliceReturnCfg returnLabel
        (literalWordMacroCfg n .done
          ⟨n / 2 ^ query.length,
            lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_succ_self n)⟩
          query []
          ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result))
        ambient rightStacks) := by
  apply transport_haltingMacroCfg_and_return (literalWordProgram n) .done
    (by rfl) returnLabel right
  · simpa [literalWordProgram, literalWordMacroCfg, literalWordCfg,
      literalWordMachine] using literalWord_correct_exact n query result
  rfl

theorem lookupScan_found_spliced {Kx Λx τ : Type}
    [DecidableEq (Sum LookupScanStack Kx)]
    (w query value : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hfind : m.find? query = some value) (processed : List SparseSymbol)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum LookupScanStack Kx => SparseSymbol)
      (Sum LookupScanLabel Λx) (LookupCellControl × τ))
    (ambient : τ) (rightStacks : Kx → List SparseSymbol) :
    ∃ n ≤ m.length * (12 * w + 22) + 11 * w + processed.length + 22,
      ((fun o => o.bind (TM2.step (spliceLeftProgram lookupScanProgram
        .found returnLabel right)))^[n + 1])
        (some (embedLeftCfg
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])
          ambient rightStacks)) =
        some (spliceReturnCfg returnLabel
          (lookupScanMacroCfg .found true
            (processed.reverse ++ encodeSparseMemory w m ++ [.memoryEnd]) []
            ((fixedBits w value).reverse.map SparseSymbol.bit) []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          ambient rightStacks) := by
  rcases lookupScan_found w query value hq m hm hfind processed with
    ⟨steps, hsteps, hrun⟩
  refine ⟨steps, hsteps, ?_⟩
  apply transport_haltingMacroCfg_and_return lookupScanProgram .found
    (by rfl) returnLabel right
  · simpa [lookupScanProgram, lookupScanMacroCfg, lookupScanCfg,
      lookupScanMachine] using hrun
  rfl

theorem lookupScan_missing_spliced {Kx Λx τ : Type}
    [DecidableEq (Sum LookupScanStack Kx)]
    (w query : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? query = none) (equal : Bool)
    (processed : List SparseSymbol) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : Sum LookupScanStack Kx => SparseSymbol)
      (Sum LookupScanLabel Λx) (LookupCellControl × τ))
    (ambient : τ) (rightStacks : Kx → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (spliceLeftProgram lookupScanProgram
      .missing returnLabel right)))^[
        m.length * (12 * w + 22) + processed.length + 2 + 1])
      (some (embedLeftCfg
        (lookupScanMacroCfg .scan equal
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])
        ambient rightStacks)) =
      some (spliceReturnCfg returnLabel
        (lookupScanMacroCfg .missing (equal && decide m.isEmpty)
          (processed.reverse ++ encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        ambient rightStacks) := by
  apply transport_haltingMacroCfg_and_return lookupScanProgram .missing
    (by rfl) returnLabel right
  · simpa [lookupScanProgram, lookupScanMacroCfg, lookupScanCfg,
      lookupScanMachine] using
      lookupScan_all_missing w query hq m hm hmissing equal processed
  rfl

end Lax20Proofs.RamToTM
