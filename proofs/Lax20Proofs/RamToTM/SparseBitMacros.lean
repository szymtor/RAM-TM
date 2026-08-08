import Lax20Proofs.RamToTM.DivideMacro

namespace Lax20Proofs.RamToTM

open Turing TM2

/-! Sparse-symbol versions of the Boolean arithmetic components.  These are
not new algorithms: their exact executions are transported from the already
verified Boolean machines by the alphabet embedding theorem. -/

def sparseAddProgram :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode addMachine.m

def sparseAddCfg (carry : Bool) (left right result : List Bool) :=
  mapAlphabetCfg sparseBitEncode (addCfg carry left right result)

def sparseAddDoneCfg (carry : Bool) (right result : List Bool) :=
  mapAlphabetCfg sparseBitEncode (addDoneCfg carry right result)

theorem sparseAdd_reaches_done (carry : Bool) (as bs result : List Bool)
    (hlen : as.length = bs.length) :
    ((fun o => o.bind (TM2.step sparseAddProgram))^[as.length + 1])
        (some (sparseAddCfg carry as bs result)) =
      some (sparseAddDoneCfg (addCarryOut as bs carry) []
        ((addBits as bs carry).reverse ++ result)) := by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode addMachine.m
    (addMachine_reaches_done carry as bs result hlen)

def sparseZipProgram (f : Bool → Bool → Bool) :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode (zipMachine f).m

def sparseZipCfg (f : Bool → Bool → Bool) (left right result : List Bool) :=
  mapAlphabetCfg sparseBitEncode (zipCfg f left right result)

def sparseZipDoneCfg (f : Bool → Bool → Bool) (result : List Bool) :=
  mapAlphabetCfg sparseBitEncode (zipDoneCfg f result)

theorem sparseZip_reaches_done (f : Bool → Bool → Bool)
    (as bs result : List Bool) (hlen : as.length = bs.length) :
    ((fun o => o.bind (TM2.step (sparseZipProgram f)))^[as.length + 1])
        (some (sparseZipCfg f as bs result)) =
      some (sparseZipDoneCfg f ((zipBits f as bs).reverse ++ result)) := by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode (zipMachine f).m
    (zipMachine_reaches_done f as bs result hlen)

def sparseCompareProgram :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode compareMachine.m

def sparseCompareCfg (less : Bool) (left right leftBackup rightBackup : List Bool) :=
  mapAlphabetCfg sparseBitEncode (compareCfg less left right leftBackup rightBackup)

def sparseCompareDoneCfg (less : Bool) (leftBackup rightBackup : List Bool) :=
  mapAlphabetCfg sparseBitEncode (compareDoneCfg less leftBackup rightBackup)

theorem sparseCompare_fixed_correct (w a b : ℕ)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    ((fun o => o.bind (TM2.step sparseCompareProgram))^[w + 1])
        (some (sparseCompareCfg false (fixedBits w a) (fixedBits w b) [] [])) =
      some (sparseCompareDoneCfg (decide (a < b))
        (fixedBits w a).reverse (fixedBits w b).reverse) := by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode compareMachine.m
    (compareMachine_fixed_correct w a b ha hb)

def sparseSubProgram :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode subMachine.m

def sparseSubCfg (borrow : Bool) (left right result : List Bool) :=
  mapAlphabetCfg sparseBitEncode (subCfg borrow left right result)

def sparseSubDoneCfg (borrow : Bool) (result : List Bool) :=
  mapAlphabetCfg sparseBitEncode (subDoneCfg borrow result)

theorem sparseSub_fixed_correct (w : ℕ) {a b : ℕ}
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hba : b ≤ a) :
    ((fun o => o.bind (TM2.step sparseSubProgram))^[w + 1])
        (some (sparseSubCfg false (fixedBits w a) (fixedBits w b) [])) =
      some (sparseSubDoneCfg false (fixedBits w (a - b)).reverse) := by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode subMachine.m
    (subMachine_fixed_correct w ha hb hba)

def sparseShiftProgram :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode shiftMachine.m

def sparseShiftCfg (label : ShiftLabel) (source temp result : List Bool) :=
  mapAlphabetCfg sparseBitEncode (shiftCfg label source temp result)

theorem sparseShift_correct_nonempty (a : Bool) (as : List Bool) :
    ((fun o => o.bind (TM2.step sparseShiftProgram))^[2 * (a :: as).length + 3])
        (some (sparseShiftCfg .first (a :: as) [] [])) =
      some (sparseShiftCfg .done [] [] (shiftLeftBits (a :: as))) := by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode shiftMachine.m
    (shiftMachine_correct_nonempty a as)

def sparseMulProgram :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode mulMachine.m

def sparseMulOuterCfg (multiplier multiplicand accumulator : List Bool) :=
  mapAlphabetCfg sparseBitEncode (mulOuterCfg multiplier multiplicand accumulator)

def sparseMulDoneCfg (multiplicand accumulator : List Bool) :=
  mapAlphabetCfg sparseBitEncode (mulDoneCfg multiplicand accumulator)

theorem sparseMul_fixed_correct (w a b : ℕ) (hw : 0 < w)
    (hb : b < 2 ^ w) :
    ∃ finalMultiplicand : List Bool,
      ((fun o => o.bind (TM2.step sparseMulProgram))^[
        mulRunTime (fixedBits w b) w])
        (some (sparseMulOuterCfg (fixedBits w b) (fixedBits w a) (fixedBits w 0))) =
      some (sparseMulDoneCfg finalMultiplicand (fixedBits w (a * b))) := by
  rcases mulMachine_fixed_correct w a b hw hb with ⟨final, hrun⟩
  refine ⟨final, ?_⟩
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode mulMachine.m hrun

theorem sparseMul_fixed_correct_with_length (w a b : ℕ) (hw : 0 < w)
    (hb : b < 2 ^ w) :
    ∃ finalMultiplicand : List Bool, finalMultiplicand.length = w ∧
      ((fun o => o.bind (TM2.step sparseMulProgram))^[
        mulRunTime (fixedBits w b) w])
        (some (sparseMulOuterCfg (fixedBits w b) (fixedBits w a) (fixedBits w 0))) =
      some (sparseMulDoneCfg finalMultiplicand (fixedBits w (a * b))) := by
  rcases mulMachine_fixed_correct_with_length w a b hw hb with
    ⟨final, hlen, hrun⟩
  refine ⟨final, hlen, ?_⟩
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode mulMachine.m hrun

def sparseDivProgram :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode divMachine.m

def sparseDivInitialCfg (dividend divisor remainder : List Bool) :=
  mapAlphabetCfg sparseBitEncode (divInitialCfg dividend divisor remainder)

def sparseDivDoneCfg (divisorNonzero : Bool)
    (divisor remainder quotient : List Bool) :=
  mapAlphabetCfg sparseBitEncode
    (divDoneCfg divisorNonzero divisor remainder quotient)

theorem sparseDiv_zero_correct (w a : ℕ) :
    ((fun o => o.bind (TM2.step sparseDivProgram))^[divZeroRunTime w])
      (some (sparseDivInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) 0)
        (fixedBits (w + 1) 0))) =
      some (sparseDivDoneCfg false (fixedBits (w + 1) 0) (fixedBits (w + 1) 0)
        (fixedBits w 0)) := by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode divMachine.m (divMachine_zero_correct w a)

theorem sparseDiv_positive_correct (w a d : ℕ)
    (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w) :
    ((fun o => o.bind (TM2.step sparseDivProgram))^[divPositiveRunTime w])
      (some (sparseDivInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) d)
        (fixedBits (w + 1) 0))) =
      some (sparseDivDoneCfg true (fixedBits (w + 1) d)
        (fixedBits (w + 1) (a % d)) (fixedBits w (a / d))) := by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode divMachine.m
    (divMachine_positive_correct w a d ha hd0 hd)

end Lax20Proofs.RamToTM
