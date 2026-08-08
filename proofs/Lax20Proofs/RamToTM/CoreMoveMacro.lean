import Lax20Proofs.RamToTM.MemoryWriteCoreMacro

namespace Lax20Proofs.RamToTM

open Turing TM2

def symbolMoveCoreEncode (source target : CoreStack) : SymbolMoveStack → CoreStack
  | .source => source
  | .target => target

def symbolMoveCoreDecode (source target : CoreStack) : CoreStack → Option SymbolMoveStack :=
  fun k => if k = source then some .source
    else if k = target then some .target else none

def symbolMoveCoreRenaming (source target : CoreStack) (hne : source ≠ target) :
    StackRenaming SymbolMoveStack CoreStack where
  encode := symbolMoveCoreEncode source target
  decode := symbolMoveCoreDecode source target
  decode_encode := by
    intro k
    cases k
    · simp [symbolMoveCoreDecode, symbolMoveCoreEncode]
    · simp [symbolMoveCoreDecode, symbolMoveCoreEncode, hne, Ne.symm hne]
  encode_decode := by
    intro k' k h
    cases k with
    | source =>
        have hs : k' = source := by
          by_cases hs : k' = source
          · exact hs
          · simp [symbolMoveCoreDecode, hs] at h
        exact hs.symm
    | target =>
        have ht : k' = target := by
          by_cases hs : k' = source
          · subst k'
            simp [symbolMoveCoreDecode, hne] at h
          · by_cases ht : k' = target
            · exact ht
            · simp [symbolMoveCoreDecode, hs, ht] at h
        exact ht.symm

def symbolMoveCoreProgram : SymbolMoveLabel →
    TM2.Stmt (fun _ : SymbolMoveStack => SparseSymbol)
      SymbolMoveLabel SymbolMoveControl :=
  fun label => symbolMoveMachine.m label

def symbolMoveLocalCfg (label : SymbolMoveLabel)
    (source target : List SparseSymbol) :
    TM2.Cfg (fun _ : SymbolMoveStack => SparseSymbol)
      SymbolMoveLabel SymbolMoveControl where
  l := some label
  var := default
  stk := symbolMoveStacks source target

def symbolMoveLocalCfgState (label : SymbolMoveLabel)
    (state : SymbolMoveControl) (source target : List SparseSymbol) :
    TM2.Cfg (fun _ : SymbolMoveStack => SparseSymbol)
      SymbolMoveLabel SymbolMoveControl where
  l := some label
  var := state
  stk := symbolMoveStacks source target

theorem symbolMoveLocal_correct_from (state : SymbolMoveControl)
    (source target : List SparseSymbol) :
    ((fun o => o.bind (TM2.step symbolMoveCoreProgram))^[source.length + 1])
      (some (symbolMoveLocalCfgState .loop state source target)) =
      some (symbolMoveLocalCfg .done [] (source.reverse ++ target)) := by
  change ((fun o : Option symbolMoveMachine.Cfg =>
      o.bind symbolMoveMachine.step)^[source.length + 1])
      (some (symbolMoveCfgState state source target)) =
      some (symbolMoveDoneCfg (source.reverse ++ target))
  exact symbolMove_reaches_done_from state source target

theorem symbolMoveLocal_correct (source target : List SparseSymbol) :
    ((fun o => o.bind (TM2.step symbolMoveCoreProgram))^[source.length + 1])
      (some (symbolMoveLocalCfg .loop source target)) =
      some (symbolMoveLocalCfg .done [] (source.reverse ++ target)) := by
  have hp : symbolMoveCoreProgram = symbolMoveMachine.m := by
    funext l
    rfl
  rw [hp]
  simpa [symbolMoveLocalCfg, symbolMoveCfg, symbolMoveDoneCfg] using
    symbolMove_reaches_done source target

theorem symbolMove_core_correct {Λx τ : Type}
    (sourceStack targetStack : CoreStack) (hne : sourceStack ≠ targetStack)
    (source target : List SparseSymbol) (returnLabel : Λx)
    (ambientProgram : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum SymbolMoveLabel Λx) (SymbolMoveControl × τ))
    (ambientState : τ) (ambientStacks : CoreStack → List SparseSymbol) :
    ((fun o => o.bind (TM2.step (renamedSpliceProgram
      (symbolMoveCoreRenaming sourceStack targetStack hne)
      symbolMoveCoreProgram .done returnLabel ambientProgram)))^[source.length + 2])
      (some (renamedCfg (symbolMoveCoreRenaming sourceStack targetStack hne)
        (symbolMoveLocalCfg .loop source target) ambientState ambientStacks)) =
      some (renamedReturnCfg (symbolMoveCoreRenaming sourceStack targetStack hne)
        returnLabel (symbolMoveLocalCfg .done [] (source.reverse ++ target))
        ambientState ambientStacks) := by
  convert transport_renamedHaltingMacro_and_return
    (symbolMoveCoreRenaming sourceStack targetStack hne)
    symbolMoveCoreProgram .done (by rfl) returnLabel ambientProgram
    (symbolMoveLocal_correct source target) rfl ambientState ambientStacks
    using 1 <;> omega

end Lax20Proofs.RamToTM
