import Lax20Proofs.RamToTM.DirectOperandPipeline

namespace Lax20Proofs.RamToTM

open Turing TM2

/-! The literal branch of operand evaluation, with exactly the same boundary
contract as the memory branches: the accumulator and encoded memory are
preserved, all scratch stacks are empty, and the low word of the operand is
returned (least-significant end first) on `work0`.  The quotient retained in
the finite control records whether a program literal exceeded the word. -/

def literalOperandProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    Sum LiteralWordLabel R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol)
      (Sum LiteralWordLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft literalWordCoreRenaming FullInterpreterState.literalLens
      (boundedLiteralWordProgram N) .done returnLabel)
    right

def literalOperandStartCfg {N : ℕ} {R : Type}
    (n : ℕ) (hn : n ≤ N) (w accumulator : ℕ)
    (m : SparseMemory) (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (Sum LiteralWordLabel R) (FullInterpreterState N) :=
  lensRenamedCfg literalWordCoreRenaming FullInterpreterState.literalLens
    (boundedLiteralWordCfg N .emit ⟨n, by omega⟩
      ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
    state (operandBoundaryBase w accumulator m base)

theorem literalOperand_return_bridge {N : ℕ} {R : Type}
    (n : ℕ) (hn : n ≤ N) (w accumulator : ℕ)
    (m : SparseMemory) (returnLabel : R)
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    phaseReturnCfg literalWordCoreRenaming FullInterpreterState.literalLens
      returnLabel
      (boundedLiteralWordCfg N .done
        ⟨n / 2 ^ w, by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
        ((fixedBits w accumulator).map SparseSymbol.bit) []
        ((fixedBits w n).reverse.map SparseSymbol.bit))
      state (operandBoundaryBase w accumulator m base) =
    cleanReturnCfg returnLabel
        (FullInterpreterState.literalLens.put state
          ⟨none, ⟨n / 2 ^ w, by
            exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
        (operandResultBase w accumulator (n % 2 ^ w) m base) := by
  simp [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    literalWordCoreRenaming, literalWordCoreDecode, boundedLiteralWordCfg,
    literalWordStacks, operandBoundaryBase, operandResultBase,
    renamedStacks, fixedBits_mod_word]
  funext k
  cases k <;> simp [renamedStacks, literalWordCoreRenaming,
    literalWordCoreDecode, boundedLiteralWordCfg, literalWordStacks,
    operandBoundaryBase, operandResultBase, fixedBits_mod_word,
    List.map_reverse]

theorem literalOperand_correct {N : ℕ} {R : Type}
    (n : ℕ) (hn : n ≤ N) (w accumulator : ℕ)
    (m : SparseMemory) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state : FullInterpreterState N)
    (base : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step
      (literalOperandProgram returnLabel right)))^[2 * w + 3])
      (some (literalOperandStartCfg (R := R) n hn w accumulator m state base)) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.literalLens.put state
          ⟨none, ⟨n / 2 ^ w, by
            exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
        (operandResultBase w accumulator (operandWordValue w (.lit n) m)
          m base))) := by
  have h := run_lensPhase_to_right literalWordCoreRenaming
    FullInterpreterState.literalLens (boundedLiteralWordProgram N)
    .done (by rfl) returnLabel right
    (boundedLiteralWord_correct_exact N n hn
      ((fixedBits w accumulator).map SparseSymbol.bit) []) rfl
    state (operandBoundaryBase w accumulator m base)
  simp only [List.length_map, fixedBits_length, List.append_nil] at h
  rw [literalOperand_return_bridge n hn w accumulator m returnLabel state base]
    at h
  simpa [literalOperandProgram, literalOperandStartCfg, operandWordValue] using h

theorem transport_iterate_literal_right {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps : Nat}
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun : ((fun o => o.bind (TM2.step right))^[steps])
      (some c) = some d) :
    ((fun o => o.bind (TM2.step
      (literalOperandProgram returnLabel right)))^[steps])
      (some (mapLabelCfg Sum.inr c)) =
    some (mapLabelCfg Sum.inr d) := by
  exact transport_iterate_liftRightProgram
    (lensPhaseLeft literalWordCoreRenaming FullInterpreterState.literalLens
      (boundedLiteralWordProgram N) .done returnLabel)
    right hrun

end Lax20Proofs.RamToTM
