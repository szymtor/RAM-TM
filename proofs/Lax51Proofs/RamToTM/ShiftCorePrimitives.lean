import Lax51Proofs.RamToTM.ShiftRightMacro
import Lax51Proofs.RamToTM.FullInterpreterState

namespace Lax51Proofs.RamToTM

open Turing TM2

def sparseShiftLeftCoreProgram : ShiftLabel ->
    TM2.Stmt (fun _ : ShiftStack => SparseSymbol) ShiftLabel MoveControl :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode shiftMachine.m

def sparseShiftLeftLocalCfg (label : ShiftLabel)
    (source temp result : List Bool) :
    TM2.Cfg (fun _ : ShiftStack => SparseSymbol) ShiftLabel MoveControl :=
  mapAlphabetCfg sparseBitEncode (shiftCfg label source temp result)

theorem sparseShiftLeftLocal_correct_nonempty (a : Bool) (as : List Bool) :
    ((fun x => x.bind (TM2.step sparseShiftLeftCoreProgram))^[
      2 * (a :: as).length + 3])
      (some (sparseShiftLeftLocalCfg .first (a :: as) [] [])) =
    some (sparseShiftLeftLocalCfg .done [] []
      (shiftLeftBits (a :: as))) := by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode shiftMachine.m
    (shiftMachine_correct_nonempty a as)

def sparseShiftRightCoreProgram : ShiftRightLabel ->
    TM2.Stmt (fun _ : ShiftStack => SparseSymbol) ShiftRightLabel MoveControl :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode shiftRightMachine.m

def sparseShiftRightLocalCfg (label : ShiftRightLabel)
    (source temp result : List Bool) :
    TM2.Cfg (fun _ : ShiftStack => SparseSymbol) ShiftRightLabel MoveControl :=
  mapAlphabetCfg sparseBitEncode (shiftRightCfg label source temp result)

theorem sparseShiftRightLocal_correct_nonempty (a : Bool) (as : List Bool) :
    ((fun x => x.bind (TM2.step sparseShiftRightCoreProgram))^[
      2 * (a :: as).length + 2])
      (some (sparseShiftRightLocalCfg .discard (a :: as) [] [])) =
    some (sparseShiftRightLocalCfg .done [] []
      (shiftRightBits (a :: as))) := by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode shiftRightMachine.m
    (shiftRightMachine_correct_nonempty a as)

end Lax51Proofs.RamToTM
