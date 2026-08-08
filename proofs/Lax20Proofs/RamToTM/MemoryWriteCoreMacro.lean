import Lax20Proofs.RamToTM.DivideCoreMacro

namespace Lax20Proofs.RamToTM

open Turing TM2

def prependCoreEncode : PrependCellStack → CoreStack
  | .address => .work0
  | .value => .work1
  | .memory => .memory

def prependCoreDecode : CoreStack → Option PrependCellStack
  | .work0 => some .address
  | .work1 => some .value
  | .memory => some .memory
  | _ => none

def prependCoreRenaming : StackRenaming PrependCellStack CoreStack where
  encode := prependCoreEncode
  decode := prependCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [prependCoreDecode, prependCoreEncode] at h ⊢

def prependCoreProgram : PrependCellLabel →
    TM2.Stmt (fun _ : PrependCellStack => SparseSymbol)
      PrependCellLabel PrependCellControl :=
  fun label => prependCellMachine.m label

def prependLocalCfg (label : PrependCellLabel)
    (address value memory : List SparseSymbol) :
    TM2.Cfg (fun _ : PrependCellStack => SparseSymbol)
      PrependCellLabel PrependCellControl where
  l := some label
  var := default
  stk := prependCellStacks address value memory

theorem prependLocal_fixed_correct (w a v : ℕ) (memory : List SparseSymbol) :
    ((fun o => o.bind (TM2.step prependCoreProgram))^[2 * w + 5])
      (some (prependLocalCfg .cellEnd
        ((fixedBits w a).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit) memory)) =
      some (prependLocalCfg .done [] [] (encodeSparseCell w (a, v) ++ memory)) := by
  have hp : prependCoreProgram = prependCellMachine.m := by
    funext l
    rfl
  rw [hp]
  simpa [prependLocalCfg, prependCellCfg] using
    prependCell_fixed_correct w a v memory

theorem prepend_core_fixed_correct {Λx τ : Type}
    (w a v : ℕ) (memory : List SparseSymbol) (returnLabel : Λx)
    (ambientProgram : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum PrependCellLabel Λx) (PrependCellControl × τ))
    (ambientState : τ) (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (renamedSpliceProgram prependCoreRenaming
      prependCoreProgram .done returnLabel ambientProgram)))^[2 * w + 6])
      (some (renamedCfg prependCoreRenaming
        (prependLocalCfg .cellEnd
          ((fixedBits w a).reverse.map SparseSymbol.bit)
          ((fixedBits w v).reverse.map SparseSymbol.bit) memory)
        ambientState ambientStacks)) =
      some (renamedReturnCfg prependCoreRenaming returnLabel
        (prependLocalCfg .done [] [] (encodeSparseCell w (a, v) ++ memory))
        ambientState ambientStacks) := by
  convert transport_renamedHaltingMacro_and_return prependCoreRenaming
    prependCoreProgram .done (by rfl) returnLabel ambientProgram
    (prependLocal_fixed_correct w a v memory) rfl ambientState ambientStacks
    using 1 <;> omega

end Lax20Proofs.RamToTM
