import Lax51Proofs.RamToTM.CleanLookupPipeline

namespace Lax51Proofs.RamToTM

open Turing TM2

/-! Preserve a reversed word while changing its work tape.  One stack move
reverses, so indirect addressing uses two moves via `work2`. -/

def lookupQueryBase (w accumulator query : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol) : CoreStack → List SparseSymbol :=
  fun
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work1 => (fixedBits w query).reverse.map SparseSymbol.bit
  | .work0 | .work2 | .work3 | .work4
  | .work5 | .work6 | .work7 => []
  | k => base k

abbrev QueryTransferTail (R : Type) := Sum SymbolMoveLabel R
abbrev QueryTransferLabel (R : Type) :=
  Sum SymbolMoveLabel (QueryTransferTail R)

def queryTransferTailProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    QueryTransferTail R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (QueryTransferTail R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work2 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def queryTransferProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    QueryTransferLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (QueryTransferLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (queryTransferTailProgram returnLabel right)

theorem queryTransfer_bridge {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (m : SparseMemory)
    (base : CoreStack → List SparseSymbol)
    (state : FullInterpreterState N) :
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl SymbolMoveLabel.loop : QueryTransferTail R)
      (symbolMoveLocalCfg .done []
        ((fixedBits w query).map SparseSymbol.bit))
      state (operandResultBase w accumulator query m base) =
    lensRenamedCfg (Λx := R)
      (symbolMoveCoreRenaming .work2 .work1 (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((fixedBits w query).map SparseSymbol.bit) [])
      (FullInterpreterState.moveLens.put state default)
      (lookupQueryBase w accumulator query m base) := by
  simp [phaseReturnCfg, lensRenamedCfg, operandResultBase, lookupQueryBase,
    renamedStacks, symbolMoveCoreRenaming, symbolMoveCoreDecode,
    symbolMoveLocalCfg, symbolMoveStacks, List.map_reverse]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks, symbolMoveCoreRenaming,
      symbolMoveCoreDecode, symbolMoveLocalCfg, symbolMoveStacks,
      operandResultBase, lookupQueryBase, List.map_reverse]

theorem queryTransfer_correct {N : ℕ} {R : Type}
    (w accumulator query : ℕ) (m : SparseMemory)
    (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step
      (queryTransferProgram returnLabel right)))^[2 * w + 4])
      (some (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work2 (by decide))
        FullInterpreterState.moveLens
        (symbolMoveLocalCfgState .loop
          (FullInterpreterState.moveLens.get state)
          ((fixedBits w query).reverse.map SparseSymbol.bit) [])
        state (operandResultBase w accumulator query m base))) =
    some (mapLabelCfg (fun l : QueryTransferTail R => Sum.inr l)
      (mapLabelCfg (fun l : R => Sum.inr l)
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work2 .work1 (by decide))
          FullInterpreterState.moveLens returnLabel
          (symbolMoveLocalCfg .done []
            ((fixedBits w query).reverse.map SparseSymbol.bit))
          (FullInterpreterState.moveLens.put state default)
          (lookupQueryBase w accumulator query m base)))) := by
  have h₁ := run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .work2 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop)
    (queryTransferTailProgram returnLabel right)
    (symbolMoveLocal_correct_from
      (FullInterpreterState.moveLens.get state)
      ((fixedBits w query).reverse.map SparseSymbol.bit) []) rfl
    state (operandResultBase w accumulator query m base)
  simp only [List.length_map, List.length_reverse, fixedBits_length,
    List.append_nil, List.map_reverse, List.reverse_reverse] at h₁
  rw [queryTransfer_bridge (R := R) w accumulator query m base state] at h₁
  have h₂ := run_lensPhase_to_right
    (symbolMoveCoreRenaming .work2 .work1 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel right
    (symbolMoveLocal_correct ((fixedBits w query).map SparseSymbol.bit) []) rfl
    (FullInterpreterState.moveLens.put state default)
    (lookupQueryBase w accumulator query m base)
  simp only [List.length_map, fixedBits_length, List.append_nil,
    List.map_reverse] at h₂
  have hchain := chain_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (queryTransferTailProgram returnLabel right) h₁ h₂
  have htime : w + 2 + (w + 2) = 2 * w + 4 := by omega
  rw [htime] at hchain
  simpa [queryTransferProgram] using hchain

end Lax51Proofs.RamToTM
