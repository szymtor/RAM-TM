import Lax759944Proofs.TapeRamVirtualMemory
import Mathlib.Data.Nat.Bitwise

namespace Lax759944Proofs.TapeRamVirtualCompiler

open Lax808846.Ram TapeRamVirtualMemory

-- All compiler registers are odd physical cells. They never alias a
-- simulated cell, even when the source program uses every virtual address.
def maskRegister : Nat := 1
def twoRegister : Nat := 3
def addressRegister : Nat := 5
def leftRegister : Nat := 7
def rightRegister : Nat := 9
def resultRegister : Nat := 11

/-- Initialize the virtual mask without knowing the physical word width.
At width `v+1`, halving the physical all-ones word gives `2^v-1`. -/
def prelude : Program := [.set 1 0, .not 1 1, .set 3 2, .div 1 1 3]

/-- Read a virtual direct-addressed cell into an odd compiler register. -/
def readCell (target address : Nat) : Program :=
  [.set 5 address, .and 5 5 1, .mul 5 5 3, .load target 5]

/-- Write the result register to a virtual direct-addressed cell. -/
def writeCell (address : Nat) : Program :=
  [.set 5 address, .and 5 5 1, .mul 5 5 3, .and 11 11 1, .store 5 11]

/-- Straight-line part of one translated instruction. Sequential and indexed
input use the same original input on both machines; indexed results and lengths
are masked to the virtual width when written back. EOF branches use no body. -/
def body : Instr → Program
  | .set a value => [.set 11 value] ++ writeCell a
  | .load a b => readCell 7 b ++ [.mul 5 7 3, .load 11 5] ++ writeCell a
  | .store a b => readCell 7 a ++ readCell 11 b ++
      [.mul 5 7 3, .and 11 11 1, .store 5 11]
  | .add a b c => readCell 7 b ++ readCell 9 c ++ [.add 11 7 9] ++ writeCell a
  | .sub a b c => readCell 7 b ++ readCell 9 c ++ [.sub 11 7 9] ++ writeCell a
  | .mul a b c => readCell 7 b ++ readCell 9 c ++ [.mul 11 7 9] ++ writeCell a
  | .div a b c => readCell 7 b ++ readCell 9 c ++ [.div 11 7 9] ++ writeCell a
  | .and a b c => readCell 7 b ++ readCell 9 c ++ [.and 11 7 9] ++ writeCell a
  | .shiftl a b c => readCell 7 b ++ readCell 9 c ++ [.shiftl 11 7 9] ++ writeCell a
  | .not a b => readCell 7 b ++ [.sub 11 1 7] ++ writeCell a
  | .inputLength a => [.inputLength 11] ++ writeCell a
  | .inputLoad a b => readCell 7 b ++ [.inputLoad 11 7] ++ writeCell a
  | .read a => [.read 11] ++ writeCell a
  | .write a => readCell 11 a ++ [.write 11]
  | .jzero a _ => readCell 11 a
  | .jump _ | .jeof _ | .halt => []

theorem body_length_le (i : Instr) : (body i).length ≤ 16 := by
  cases i <;> simp [body, readCell, writeCell]

/-- Every translated straight-line body occupies exactly sixteen slots.
Padding touches only compiler scratch and makes branch locations uniform. -/
def paddedBody (i : Instr) : Program :=
  body i ++ List.replicate (16 - (body i).length) (.set 5 0)

@[simp] theorem paddedBody_length (i : Instr) : (paddedBody i).length = 16 := by
  simp only [paddedBody, List.length_append, List.length_replicate]
  have := body_length_le i
  omega

/-- Fixed block addresses allow jumps to be translated independently of
the source program and of the runtime word width. -/
def location (pc : Nat) : Nat := 4 + 18 * pc

def branch (pc : Nat) : Instr → Program
  | .halt => [.halt, .halt]
  | .jump target => [.jump (location target), .halt]
  | .jzero _ target => [.jzero 11 (location target), .jump (location (pc + 1))]
  | .jeof target => [.jeof (location target), .jump (location (pc + 1))]
  | _ => [.jump (location (pc + 1)), .halt]

def block (pc : Nat) (i : Instr) : Program :=
  paddedBody i ++ branch pc i

def blocks (pc : Nat) : Program → Program
  | [] => []
  | i :: rest => block pc i ++ blocks (pc + 1) rest

def compile (p : Program) : Program := prelude ++ blocks 0 p

@[simp] theorem branch_length (pc : Nat) (i : Instr) : (branch pc i).length = 2 := by
  cases i <;> rfl

@[simp] theorem block_length (pc : Nat) (i : Instr) : (block pc i).length = 18 := by
  simp [block]

@[simp] theorem blocks_length (pc : Nat) (p : Program) :
    (blocks pc p).length = 18 * p.length := by
  induction p generalizing pc with
  | nil => rfl
  | cons i rest ih => simp only [blocks, List.length_append, block_length, ih,
      List.length_cons]; omega

@[simp] theorem compile_length (p : Program) : (compile p).length = location p.length := by
  simp [compile, prelude, location]
  omega

theorem blocks_get (p : Program) (base pc offset : Nat) (hoff : offset < 18) :
    (blocks base p)[18 * pc + offset]? =
      p[pc]?.bind (fun i => (block (base + pc) i)[offset]?) := by
  induction p generalizing base pc with
  | nil => simp [blocks]
  | cons i rest ih =>
    cases pc with
    | zero => simp [blocks, List.getElem?_append, hoff]
    | succ pc =>
      have hlarge : ¬18 * (pc + 1) + offset < 18 := by omega
      simp only [blocks, List.getElem?_append, block_length, hlarge, ↓reduceIte,
        List.getElem?_cons_succ]
      rw [show 18 * (pc + 1) + offset - 18 = 18 * pc + offset by omega, ih]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem compile_get (p : Program) (pc offset : Nat) (hoff : offset < 18) :
    (compile p)[location pc + offset]? =
      p[pc]?.bind (fun i => (block pc i)[offset]?) := by
  have hlarge : ¬location pc + offset < prelude.length := by simp [location, prelude]; omega
  simp only [compile, List.getElem?_append, hlarge, ↓reduceIte]
  have hsub : location pc + offset - prelude.length = 18 * pc + offset := by
    simp [location, prelude]; omega
  rw [hsub, blocks_get p 0 pc offset hoff, Nat.zero_add]

theorem compile_get_paddedBody (p : Program) (pc : Nat) (i : Instr)
    (hfetch : p[pc]? = some i) (offset : Nat) (hoff : offset < 16) :
    (compile p)[location pc + offset]? = (paddedBody i)[offset]? := by
  rw [compile_get p pc offset (by omega), hfetch]
  simp [block, List.getElem?_append, hoff]

theorem compile_get_branch (p : Program) (pc : Nat) (i : Instr)
    (hfetch : p[pc]? = some i) (offset : Nat) (hoff : offset < 2) :
    (compile p)[location pc + 16 + offset]? = (branch pc i)[offset]? := by
  rw [show location pc + 16 + offset = location pc + (16 + offset) by omega,
    compile_get p pc (16 + offset) (by omega), hfetch]
  simp [block, List.getElem?_append, hoff]

/-- Masking a physical arithmetic result gives the exact virtual result. -/
theorem mask_result (v value : Nat) :
    Nat.land (value % 2 ^ (v + 1)) (2 ^ v - 1) = value % 2 ^ v := by
  change ((value % 2 ^ (v + 1)) &&& (2 ^ v - 1)) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, mod_physical_virtual]

theorem half_all_ones (v : Nat) : (2 ^ (v + 1) - 1) / 2 = 2 ^ v - 1 := by
  have := Nat.two_pow_pos v
  rw [Nat.pow_succ]
  omega

end Lax759944Proofs.TapeRamVirtualCompiler
