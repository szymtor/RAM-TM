import Lax51Proofs.RamToTM.InterpreterStackRenamings

namespace Lax51Proofs.RamToTM

/-! Concrete placements of the arithmetic macro stacks in `CoreStack`. -/

def binaryCoreEncode : AddStack → CoreStack
  | .left => .accumulator
  | .right => .work1
  | .result => .work0

def binaryCoreDecode : CoreStack → Option AddStack
  | .accumulator => some .left
  | .work1 => some .right
  | .work0 => some .result
  | _ => none

def binaryCoreRenaming : StackRenaming AddStack CoreStack where
  encode := binaryCoreEncode
  decode := binaryCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [binaryCoreDecode, binaryCoreEncode] at h ⊢

def shiftCoreEncode : ShiftStack → CoreStack
  | .source => .accumulator
  | .temp => .work1
  | .result => .work0

def shiftCoreDecode : CoreStack → Option ShiftStack
  | .accumulator => some .source
  | .work1 => some .temp
  | .work0 => some .result
  | _ => none

def shiftCoreRenaming : StackRenaming ShiftStack CoreStack where
  encode := shiftCoreEncode
  decode := shiftCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [shiftCoreDecode, shiftCoreEncode] at h ⊢

def mulCoreEncode : MulStack → CoreStack
  | .multiplier => .work1
  | .multiplicand => .accumulator
  | .accumulator => .work0
  | .multiplicandBackup => .work2
  | .sumReverse => .work3
  | .shiftTemp => .work4

def mulCoreDecode : CoreStack → Option MulStack
  | .work1 => some .multiplier
  | .accumulator => some .multiplicand
  | .work0 => some .accumulator
  | .work2 => some .multiplicandBackup
  | .work3 => some .sumReverse
  | .work4 => some .shiftTemp
  | _ => none

def mulCoreRenaming : StackRenaming MulStack CoreStack where
  encode := mulCoreEncode
  decode := mulCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [mulCoreDecode, mulCoreEncode] at h ⊢

def divCoreEncode : DivStack → CoreStack
  | .dividend => .accumulator
  | .divisor => .work1
  | .remainder => .work2
  | .quotient => .work0
  | .divisorBackup => .work3
  | .remainderBackup => .work4
  | .differenceReverse => .work5
  | .shiftTemp => .work6

def divCoreDecode : CoreStack → Option DivStack
  | .accumulator => some .dividend
  | .work1 => some .divisor
  | .work2 => some .remainder
  | .work0 => some .quotient
  | .work3 => some .divisorBackup
  | .work4 => some .remainderBackup
  | .work5 => some .differenceReverse
  | .work6 => some .shiftTemp
  | _ => none

def divCoreRenaming : StackRenaming DivStack CoreStack where
  encode := divCoreEncode
  decode := divCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [divCoreDecode, divCoreEncode] at h ⊢

@[simp] theorem renamedStacks_binary_left
    (inner : AddStack → List SparseSymbol) (ambient : CoreStack → List SparseSymbol) :
    renamedStacks binaryCoreRenaming inner ambient .accumulator = inner .left := by rfl

@[simp] theorem renamedStacks_binary_result
    (inner : AddStack → List SparseSymbol) (ambient : CoreStack → List SparseSymbol) :
    renamedStacks binaryCoreRenaming inner ambient .work0 = inner .result := by rfl

@[simp] theorem renamedStacks_mul_result
    (inner : MulStack → List SparseSymbol) (ambient : CoreStack → List SparseSymbol) :
    renamedStacks mulCoreRenaming inner ambient .work0 = inner .accumulator := by rfl

@[simp] theorem renamedStacks_div_quotient
    (inner : DivStack → List SparseSymbol) (ambient : CoreStack → List SparseSymbol) :
    renamedStacks divCoreRenaming inner ambient .work0 = inner .quotient := by rfl

end Lax51Proofs.RamToTM
