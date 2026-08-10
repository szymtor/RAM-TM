import Lax51Proofs.RamToTM.StackRenaming

namespace Lax51Proofs.RamToTM

open Turing TM2

/-! Concrete, collision-free placements of operand-evaluation macro stacks
inside the global RAM-interpreter stack set. -/

def literalWordCoreEncode : LiteralWordStack → CoreStack
  | .query => .accumulator
  | .backup => .work7
  | .result => .work0

def literalWordCoreDecode : CoreStack → Option LiteralWordStack
  | .accumulator => some .query
  | .work7 => some .backup
  | .work0 => some .result
  | _ => none

def literalWordCoreRenaming : StackRenaming LiteralWordStack CoreStack where
  encode := literalWordCoreEncode
  decode := literalWordCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [literalWordCoreDecode,
      literalWordCoreEncode] at h ⊢

def literalQueryCoreEncode : LiteralWordStack → CoreStack
  | .query => .accumulator
  | .backup => .work7
  | .result => .work1

def literalQueryCoreDecode : CoreStack → Option LiteralWordStack
  | .accumulator => some .query
  | .work7 => some .backup
  | .work1 => some .result
  | _ => none

def literalQueryCoreRenaming : StackRenaming LiteralWordStack CoreStack where
  encode := literalQueryCoreEncode
  decode := literalQueryCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [literalQueryCoreDecode,
      literalQueryCoreEncode] at h ⊢

def zeroWordCoreEncode : ZeroWordStack → CoreStack
  | .query => .accumulator
  | .backup => .work7
  | .result => .work0

def zeroWordCoreDecode : CoreStack → Option ZeroWordStack
  | .accumulator => some .query
  | .work7 => some .backup
  | .work0 => some .result
  | _ => none

def zeroWordCoreRenaming : StackRenaming ZeroWordStack CoreStack where
  encode := zeroWordCoreEncode
  decode := zeroWordCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [zeroWordCoreDecode,
      zeroWordCoreEncode] at h ⊢

def lookupCoreEncode : LookupScanStack → CoreStack
  | .source => .memory
  | .value => .work0
  | .query => .work1
  | .address => .work2
  | .cellBackup => .work3
  | .addressBackup => .work4
  | .queryBackup => .work5
  | .processed => .work6
  | .trash => .work7

def lookupCoreDecode : CoreStack → Option LookupScanStack
  | .memory => some .source
  | .work0 => some .value
  | .work1 => some .query
  | .work2 => some .address
  | .work3 => some .cellBackup
  | .work4 => some .addressBackup
  | .work5 => some .queryBackup
  | .work6 => some .processed
  | .work7 => some .trash
  | _ => none

def lookupCoreRenaming : StackRenaming LookupScanStack CoreStack where
  encode := lookupCoreEncode
  decode := lookupCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [lookupCoreDecode, lookupCoreEncode] at h ⊢

@[simp] theorem renamedStacks_literal_accumulator
    (inner : LiteralWordStack → List SparseSymbol)
    (ambient : CoreStack → List SparseSymbol) :
    renamedStacks literalWordCoreRenaming inner ambient .accumulator =
      inner .query := by rfl

@[simp] theorem renamedStacks_literal_result
    (inner : LiteralWordStack → List SparseSymbol)
    (ambient : CoreStack → List SparseSymbol) :
    renamedStacks literalWordCoreRenaming inner ambient .work0 =
      inner .result := by rfl

@[simp] theorem renamedStacks_literalQuery_result
    (inner : LiteralWordStack → List SparseSymbol)
    (ambient : CoreStack → List SparseSymbol) :
    renamedStacks literalQueryCoreRenaming inner ambient .work1 =
      inner .result := by rfl

@[simp] theorem renamedStacks_zero_query
    (inner : ZeroWordStack → List SparseSymbol)
    (ambient : CoreStack → List SparseSymbol) :
    renamedStacks zeroWordCoreRenaming inner ambient .accumulator =
      inner .query := by rfl

@[simp] theorem renamedStacks_zero_result
    (inner : ZeroWordStack → List SparseSymbol)
    (ambient : CoreStack → List SparseSymbol) :
    renamedStacks zeroWordCoreRenaming inner ambient .work0 =
      inner .result := by rfl

@[simp] theorem renamedStacks_lookup_memory
    (inner : LookupScanStack → List SparseSymbol)
    (ambient : CoreStack → List SparseSymbol) :
    renamedStacks lookupCoreRenaming inner ambient .memory = inner .source := by rfl

@[simp] theorem renamedStacks_lookup_value
    (inner : LookupScanStack → List SparseSymbol)
    (ambient : CoreStack → List SparseSymbol) :
    renamedStacks lookupCoreRenaming inner ambient .work0 = inner .value := by rfl

@[simp] theorem renamedStacks_lookup_query
    (inner : LookupScanStack → List SparseSymbol)
    (ambient : CoreStack → List SparseSymbol) :
    renamedStacks lookupCoreRenaming inner ambient .work1 = inner .query := by rfl

theorem literalWord_core_correct {Λx τ : Type} (n : ℕ)
    (query result : List SparseSymbol) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum LiteralWordLabel Λx) (LiteralWordControl n × τ))
    (ambientState : τ) (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (renamedSpliceProgram literalWordCoreRenaming
      (literalWordProgram n) .done returnLabel right)))^[
        2 * query.length + 2 + 1])
      (some (renamedCfg literalWordCoreRenaming
        (literalWordMacroCfg n .emit ⟨n, Nat.lt_succ_self n⟩ query [] result)
        ambientState ambientStacks)) =
      some (renamedReturnCfg literalWordCoreRenaming returnLabel
        (literalWordMacroCfg n .done
          ⟨n / 2 ^ query.length,
            lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_succ_self n)⟩
          query []
          ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result))
        ambientState ambientStacks) := by
  apply transport_renamedHaltingMacro_and_return literalWordCoreRenaming
    (literalWordProgram n) .done (by rfl) returnLabel right
  · simpa [literalWordProgram, literalWordMacroCfg, literalWordCfg,
      literalWordMachine] using literalWord_correct_exact n query result
  · rfl

theorem lookup_core_found {Λx τ : Type}
    (w query value : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hfind : m.find? query = some value) (processed : List SparseSymbol)
    (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum LookupScanLabel Λx) (LookupCellControl × τ))
    (ambientState : τ) (ambientStacks : CoreStack → List SparseSymbol) :
    ∃ steps ≤ m.length * (12 * w + 22) + 11 * w + processed.length + 22,
      ((fun o => o.bind (TM2.step (renamedSpliceProgram lookupCoreRenaming
        lookupScanProgram .found returnLabel right)))^[steps + 1])
        (some (renamedCfg lookupCoreRenaming
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])
          ambientState ambientStacks)) =
        some (renamedReturnCfg lookupCoreRenaming returnLabel
          (lookupScanMacroCfg .found true
            (processed.reverse ++ encodeSparseMemory w m ++ [.memoryEnd]) []
            ((fixedBits w value).reverse.map SparseSymbol.bit) []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          ambientState ambientStacks) := by
  rcases lookupScan_found w query value hq m hm hfind processed with
    ⟨steps, hbound, hrun⟩
  refine ⟨steps, hbound, ?_⟩
  apply transport_renamedHaltingMacro_and_return lookupCoreRenaming
    lookupScanProgram .found (by rfl) returnLabel right
  · simpa [lookupScanProgram, lookupScanMacroCfg, lookupScanCfg,
      lookupScanMachine] using hrun
  · rfl

theorem lookup_core_missing {Λx τ : Type}
    (w query : ℕ) (hq : query < 2 ^ w)
    (m : SparseMemory) (hm : m.Normalized w)
    (hmissing : m.find? query = none) (equal : Bool)
    (processed : List SparseSymbol) (returnLabel : Λx)
    (right : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum LookupScanLabel Λx) (LookupCellControl × τ))
    (ambientState : τ) (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (renamedSpliceProgram lookupCoreRenaming
      lookupScanProgram .missing returnLabel right)))^[
        m.length * (12 * w + 22) + processed.length + 2 + 1])
      (some (renamedCfg lookupCoreRenaming
        (lookupScanMacroCfg .scan equal
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])
        ambientState ambientStacks)) =
      some (renamedReturnCfg lookupCoreRenaming returnLabel
        (lookupScanMacroCfg .missing (equal && decide m.isEmpty)
          (processed.reverse ++ encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        ambientState ambientStacks) := by
  apply transport_renamedHaltingMacro_and_return lookupCoreRenaming
    lookupScanProgram .missing (by rfl) returnLabel right
  · simpa [lookupScanProgram, lookupScanMacroCfg, lookupScanCfg,
      lookupScanMachine] using
      lookupScan_all_missing w query hq m hm hmissing equal processed
  · rfl

end Lax51Proofs.RamToTM
