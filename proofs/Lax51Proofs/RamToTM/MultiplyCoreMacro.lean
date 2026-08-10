import Lax51Proofs.RamToTM.BinaryCoreMacros

namespace Lax51Proofs.RamToTM

open Turing TM2

def mulBaseProgram : MulLabel →
    TM2.Stmt (fun _ : MulStack => Bool) MulLabel MulControl
  | .outer =>
      .pop .multiplier (fun s a => { s with selected := a }) <|
        .branch (fun s => s.selected.isNone)
          (.goto fun _ => .done) (.goto fun _ => .select)
  | .select => .branch (fun s => s.selected.getD false)
      (.load (fun s => { s with carry := false, left := none, right := none }) <|
        .goto fun _ => .add)
      (.goto fun _ => .shiftFirst)
  | .add =>
      .pop .multiplicand (fun s a => { s with left := a }) <|
        .branch (fun s => s.left.isNone)
          (.goto fun _ => .restoreMultiplicand)
          (.pop .accumulator (fun s b => { s with right := b }) <|
            .push .multiplicandBackup (fun s => s.left.getD false) <|
              .push .sumReverse MulControl.sumBit <|
                .load MulControl.addAdvance <| .goto fun _ => .add)
  | .restoreMultiplicand => mulMoveIteration .multiplicandBackup .multiplicand
      .restoreMultiplicand .restoreSum
  | .restoreSum => mulMoveIteration .sumReverse .accumulator
      .restoreSum .shiftFirst
  | .shiftFirst => mulMoveIteration .multiplicand .shiftTemp
      .shiftFirst .shiftDiscard
  | .shiftDiscard =>
      .pop .shiftTemp (fun s _ => MulControl.clearHeld s) <|
        .goto fun _ => .shiftSecond
  | .shiftSecond => mulMoveIteration .shiftTemp .multiplicand
      .shiftSecond .shiftPrepend
  | .shiftPrepend => .push .multiplicand (fun _ => false) <|
      .load (fun _ => default) <| .goto fun _ => .outer
  | .done => .halt

def sparseMulCoreProgram : MulLabel →
    TM2.Stmt (fun _ : MulStack => SparseSymbol) MulLabel MulControl :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode mulBaseProgram

def sparseMulLocalOuterCfg (multiplier multiplicand accumulator : List Bool) :
    TM2.Cfg (fun _ : MulStack => SparseSymbol) MulLabel MulControl where
  l := some .outer
  var := default
  stk := mapAlphabetStacks sparseBitEncode
    (mulStacks multiplier multiplicand accumulator [] [] [])

def sparseMulLocalDoneCfg (multiplicand accumulator : List Bool) :
    TM2.Cfg (fun _ : MulStack => SparseSymbol) MulLabel MulControl where
  l := some .done
  var := default
  stk := mapAlphabetStacks sparseBitEncode
    (mulStacks [] multiplicand accumulator [] [] [])

theorem sparseMulLocal_fixed_correct (w a b : ℕ) (hw : 0 < w)
    (hb : b < 2 ^ w) :
    ∃ finalMultiplicand : List Bool,
      ((fun o => o.bind (TM2.step sparseMulCoreProgram))^[
        mulRunTime (fixedBits w b) w])
        (some (sparseMulLocalOuterCfg
          (fixedBits w b) (fixedBits w a) (fixedBits w 0))) =
      some (sparseMulLocalDoneCfg finalMultiplicand (fixedBits w (a * b))) := by
  rcases sparseMul_fixed_correct w a b hw hb with ⟨final, hrun⟩
  refine ⟨final, ?_⟩
  have hp : sparseMulCoreProgram = sparseMulProgram := by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseMulLocalOuterCfg, sparseMulLocalDoneCfg, sparseMulOuterCfg,
    sparseMulDoneCfg, mulOuterCfg, mulDoneCfg, mapAlphabetCfg] using hrun

theorem sparseMulLocal_fixed_correct_with_length (w a b : ℕ) (hw : 0 < w)
    (hb : b < 2 ^ w) :
    ∃ finalMultiplicand : List Bool, finalMultiplicand.length = w ∧
      ((fun o => o.bind (TM2.step sparseMulCoreProgram))^[
        mulRunTime (fixedBits w b) w])
        (some (sparseMulLocalOuterCfg
          (fixedBits w b) (fixedBits w a) (fixedBits w 0))) =
      some (sparseMulLocalDoneCfg finalMultiplicand (fixedBits w (a * b))) := by
  rcases sparseMul_fixed_correct_with_length w a b hw hb with
    ⟨final, hlen, hrun⟩
  refine ⟨final, hlen, ?_⟩
  have hp : sparseMulCoreProgram = sparseMulProgram := by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseMulLocalOuterCfg, sparseMulLocalDoneCfg, sparseMulOuterCfg,
    sparseMulDoneCfg, mulOuterCfg, mulDoneCfg, mapAlphabetCfg] using hrun

theorem sparseMul_core_fixed_correct {Λx τ : Type}
    (w a b : ℕ) (hw : 0 < w) (hb : b < 2 ^ w)
    (returnLabel : Λx)
    (ambientProgram : Λx → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (Sum MulLabel Λx) (MulControl × τ))
    (ambientState : τ) (ambientStacks : CoreStack → List SparseSymbol) :
    ∃ finalMultiplicand : List Bool,
      ((fun o => o.bind (TM2.step (renamedSpliceProgram mulCoreRenaming
        sparseMulCoreProgram .done returnLabel ambientProgram)))^[
          mulRunTime (fixedBits w b) w + 1])
        (some (renamedCfg mulCoreRenaming
          (sparseMulLocalOuterCfg
            (fixedBits w b) (fixedBits w a) (fixedBits w 0))
          ambientState ambientStacks)) =
      some (renamedReturnCfg mulCoreRenaming returnLabel
        (sparseMulLocalDoneCfg finalMultiplicand (fixedBits w (a * b)))
        ambientState ambientStacks) := by
  rcases sparseMulLocal_fixed_correct w a b hw hb with ⟨final, hrun⟩
  refine ⟨final, ?_⟩
  exact transport_renamedHaltingMacro_and_return mulCoreRenaming
    sparseMulCoreProgram .done (by rfl) returnLabel ambientProgram hrun rfl
    ambientState ambientStacks

end Lax51Proofs.RamToTM
