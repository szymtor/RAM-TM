import Lax51Proofs.RamToTM.FullInterpreterState
import Lax51Proofs.RamToTM.PhaseComposition

namespace Lax51Proofs.RamToTM

open Turing TM2

theorem globalBoundedLiteral_correct {R : Type} (N n : ℕ) (hn : n ≤ N)
    (query result : List SparseSymbol) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum LiteralWordLabel R) (FullInterpreterState N))
    (ambientState : FullInterpreterState N)
    (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram literalWordCoreRenaming
      FullInterpreterState.literalLens (boundedLiteralWordProgram N)
      .done returnLabel right)))^[2 * query.length + 3])
      (some (lensRenamedCfg literalWordCoreRenaming
        FullInterpreterState.literalLens
        (boundedLiteralWordCfg N .emit ⟨n, by omega⟩ query [] result)
        ambientState ambientStacks)) =
    some (lensReturnCfg literalWordCoreRenaming
      FullInterpreterState.literalLens returnLabel
      (boundedLiteralWordCfg N .done
        ⟨n / 2 ^ query.length, by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
        query []
        ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result))
      ambientState ambientStacks) := by
  convert transport_lensHaltingMacro_and_return literalWordCoreRenaming
    FullInterpreterState.literalLens (boundedLiteralWordProgram N)
    .done (by rfl) returnLabel right
    (boundedLiteralWord_correct_exact N n hn query result) rfl
    ambientState ambientStacks using 1 <;> omega

def literalOperandBase (w accumulator : ℕ)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .work0 | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem globalBoundedLiteral_fixed_correct {R : Type}
    (N n : ℕ) (hn : n ≤ N) (w accumulator : ℕ)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum LiteralWordLabel R) (FullInterpreterState N))
    (ambientState : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram literalWordCoreRenaming
      FullInterpreterState.literalLens (boundedLiteralWordProgram N)
      .done returnLabel right)))^[2 * w + 3])
      (some (lensRenamedCfg literalWordCoreRenaming
        FullInterpreterState.literalLens
        (boundedLiteralWordCfg N .emit ⟨n, by omega⟩
          ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        ambientState (literalOperandBase w accumulator base))) =
    some (lensReturnCfg literalWordCoreRenaming
      FullInterpreterState.literalLens returnLabel
      (boundedLiteralWordCfg N .done
        ⟨n / 2 ^ w, by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
        ((fixedBits w accumulator).map SparseSymbol.bit) []
        ((fixedBits w n).reverse.map SparseSymbol.bit))
      ambientState (literalOperandBase w accumulator base)) := by
  simpa using globalBoundedLiteral_correct N n hn
    ((fixedBits w accumulator).map SparseSymbol.bit) [] returnLabel right
    ambientState (literalOperandBase w accumulator base)

def literalQueryBase (w accumulator : ℕ)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .work0 | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem globalBoundedLiteral_query_correct {R : Type}
    (N n : ℕ) (hn : n ≤ N) (w accumulator : ℕ)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum LiteralWordLabel R) (FullInterpreterState N))
    (ambientState : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (lensSpliceProgram literalQueryCoreRenaming
      FullInterpreterState.literalLens (boundedLiteralWordProgram N)
      .done returnLabel right)))^[2 * w + 3])
      (some (lensRenamedCfg literalQueryCoreRenaming
        FullInterpreterState.literalLens
        (boundedLiteralWordCfg N .emit ⟨n, by omega⟩
          ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        ambientState (literalQueryBase w accumulator base))) =
    some (lensReturnCfg literalQueryCoreRenaming
      FullInterpreterState.literalLens returnLabel
      (boundedLiteralWordCfg N .done
        ⟨n / 2 ^ w, by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
        ((fixedBits w accumulator).map SparseSymbol.bit) []
        ((fixedBits w n).reverse.map SparseSymbol.bit))
      ambientState (literalQueryBase w accumulator base)) := by
  convert transport_lensHaltingMacro_and_return literalQueryCoreRenaming
    FullInterpreterState.literalLens (boundedLiteralWordProgram N)
    .done (by rfl) returnLabel right
    (boundedLiteralWord_correct_exact N n hn
      ((fixedBits w accumulator).map SparseSymbol.bit) []) rfl
    ambientState (literalQueryBase w accumulator base) using 1
  · simp
  · simp

end Lax51Proofs.RamToTM
