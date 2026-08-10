import Lax51Proofs.RamToTM.StoreIndInstruction

namespace Lax51Proofs.RamToTM

open Turing TM2

def compareCoreEncode : CompareStack -> CoreStack
  | .left => .accumulator
  | .right => .work1
  | .leftBackup => .work2
  | .rightBackup => .work3

def compareCoreDecode : CoreStack -> Option CompareStack
  | .accumulator => some .left
  | .work1 => some .right
  | .work2 => some .leftBackup
  | .work3 => some .rightBackup
  | _ => none

def compareCoreRenaming : StackRenaming CompareStack CoreStack where
  encode := compareCoreEncode
  decode := compareCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [compareCoreDecode, compareCoreEncode] at h ⊢

def sparseCompareCoreProgram : CompareLabel ->
    TM2.Stmt (fun _ : CompareStack => SparseSymbol) CompareLabel CompareControl
  | .loop => mapAlphabetStmt sparseBitEncode sparseBitDecode
      (compareIteration .left .right .leftBackup .rightBackup .loop .done)
  | .done => .halt

def sparseCompareLocalCfg (less : Bool) (left right lb rb : List Bool) :
    TM2.Cfg (fun _ : CompareStack => SparseSymbol) CompareLabel CompareControl where
  l := some .loop
  var := ⟨less, none, none⟩
  stk := mapAlphabetStacks sparseBitEncode (compareStacks left right lb rb)

def sparseCompareLocalDoneCfg (less : Bool) (lb rb : List Bool) :
    TM2.Cfg (fun _ : CompareStack => SparseSymbol) CompareLabel CompareControl where
  l := some .done
  var := ⟨less, none, none⟩
  stk := mapAlphabetStacks sparseBitEncode (compareStacks [] [] lb rb)

theorem sparseCompareLocal_fixed_correct (w a b : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    ((fun o => o.bind (TM2.step sparseCompareCoreProgram))^[w + 1])
      (some (sparseCompareLocalCfg false (fixedBits w a) (fixedBits w b) [] [])) =
    some (sparseCompareLocalDoneCfg (decide (a < b))
      (fixedBits w a).reverse (fixedBits w b).reverse) := by
  have hp : sparseCompareCoreProgram =
      sparseCompareProgram := by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseCompareLocalCfg, sparseCompareLocalDoneCfg,
    sparseCompareCfg, sparseCompareDoneCfg, compareCfg, compareDoneCfg,
    mapAlphabetCfg] using sparseCompare_fixed_correct w a b ha hb

abbrev FullCompareLabel (R : Type) := Sum CompareLabel R

def fullCompareProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullCompareLabel R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (FullCompareLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft compareCoreRenaming FullInterpreterState.compareLens
      sparseCompareCoreProgram .done returnLabel)
    right

def compareResultStacks (w a b : Nat)
    (base : CoreStack -> List SparseSymbol) : CoreStack -> List SparseSymbol
  | .accumulator | .work1 => []
  | .work2 => (fixedBits w a).reverse.map SparseSymbol.bit
  | .work3 => (fixedBits w b).reverse.map SparseSymbol.bit
  | k => base k

theorem fullCompare_return_bridge {N : Nat} {R : Type}
    (returnLabel : R) (w a b : Nat)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    phaseReturnCfg compareCoreRenaming FullInterpreterState.compareLens
      returnLabel
      (sparseCompareLocalDoneCfg (decide (a < b))
        (fixedBits w a).reverse (fixedBits w b).reverse)
      state base =
    cleanReturnCfg returnLabel
      (FullInterpreterState.compareLens.put state
        ⟨decide (a < b), none, none⟩)
      (compareResultStacks w a b base) := by
  simp only [phaseReturnCfg, cleanReturnCfg, lensRenamedCfg,
    sparseCompareLocalDoneCfg]
  have hs : renamedStacks compareCoreRenaming
      (mapAlphabetStacks sparseBitEncode
        (compareStacks [] [] (fixedBits w a).reverse (fixedBits w b).reverse))
      base = compareResultStacks w a b base := by
    funext k
    cases k <;> simp [renamedStacks, compareCoreRenaming, compareCoreDecode,
      compareStacks, mapAlphabetStacks, sparseBitEncode, compareResultStacks]
  rw [hs]

theorem fullCompare_fixed_correct {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b : Nat) (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (base : CoreStack -> List SparseSymbol) (state : FullInterpreterState N) :
    ((fun o => o.bind (TM2.step (fullCompareProgram returnLabel right)))^[w + 2])
      (some (lensRenamedCfg compareCoreRenaming FullInterpreterState.compareLens
        (sparseCompareLocalCfg false (fixedBits w a) (fixedBits w b) [] [])
        state base)) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.compareLens.put state
          ⟨decide (a < b), none, none⟩)
        (compareResultStacks w a b base))) := by
  have h := run_lensPhase_to_right compareCoreRenaming
    FullInterpreterState.compareLens sparseCompareCoreProgram .done (by rfl)
    returnLabel right (sparseCompareLocal_fixed_correct w a b ha hb) rfl
    state base
  rw [fullCompare_return_bridge returnLabel w a b base state] at h
  simpa [fullCompareProgram] using h

end Lax51Proofs.RamToTM
