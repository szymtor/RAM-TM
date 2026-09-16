import Lax759944Proofs.TapeRamVirtualSimulation

namespace Lax759944Proofs.TapeRamBufferedCompiler

open Lax808846.Ram TapeRamVirtualCompiler

/-- Snapshot storage starts at odd address 65, above all adapter registers. -/
def bufferBase : Nat := 32

def lengthRegister : Nat := 13
def cursorRegister : Nat := 15
def remainingRegister : Nat := 17
def temporaryRegister : Nat := 19
def baseRegister : Nat := 21
def oneRegister : Nat := 23
def zeroRegister : Nat := 25
def headerRegister : Nat := 27

def location (pc : Nat) : Nat := 20 + 18 * pc

/-- The supplied nonempty input begins with `h` and has length `h + extra`.
For native length-prefixed input `extra=1`; for natural-list arenas `extra=4`.
The loop snapshots the entire original list, including its first word. -/
def prelude (extra : Nat) : Program := TapeRamVirtualCompiler.prelude ++
  [.set oneRegister 1,
   .set baseRegister 65,
   .set zeroRegister 0,
   .read headerRegister,
   .set lengthRegister extra,
   .add lengthRegister headerRegister lengthRegister,
   .set cursorRegister 0,
   .store baseRegister headerRegister,
   .set temporaryRegister 67,
   .sub remainingRegister lengthRegister oneRegister,
   .jzero remainingRegister (location 0),
   .read resultRegister,
   .store temporaryRegister resultRegister,
   .add temporaryRegister temporaryRegister twoRegister,
   .sub remainingRegister remainingRegister oneRegister,
   .jump 14]

/-- All logical sequential reads come from the protected snapshot. -/
def readBody (programLength target : Nat) : Program :=
  [.sub resultRegister lengthRegister cursorRegister,
   .jzero resultRegister (location programLength),
   .mul addressRegister cursorRegister twoRegister,
   .add addressRegister addressRegister baseRegister,
   .load resultRegister addressRegister,
   .add cursorRegister cursorRegister oneRegister] ++ writeCell target

/-- Indexed reads check the source word index against the original length;
the index is sampled before writing the virtual destination. -/
def inputLoadBody (pc target index : Nat) : Program :=
  readCell resultRegister index ++
  [.sub temporaryRegister lengthRegister resultRegister,
   .jzero temporaryRegister (location pc + 10),
   .mul addressRegister resultRegister twoRegister,
   .add addressRegister addressRegister baseRegister,
   .load resultRegister addressRegister,
   .jump (location pc + 11),
   .set resultRegister 0] ++ writeCell target

def body (programLength pc : Nat) : Instr → Program
  | .read target => readBody programLength target
  | .inputLength target => [.add resultRegister lengthRegister zeroRegister] ++ writeCell target
  | .inputLoad target index => inputLoadBody pc target index
  | .jeof _ => [.sub resultRegister lengthRegister cursorRegister]
  | instruction => TapeRamVirtualCompiler.body instruction

/-- Instructions whose body uses only the generic memory/output compiler. -/
def CoreInstruction : Instr → Prop
  | .read _ | .inputLength _ | .inputLoad _ _ | .jeof _ => False
  | _ => True

theorem body_eq_of_core (programLength pc : Nat) (instruction : Instr)
    (hcore : CoreInstruction instruction) :
    body programLength pc instruction = TapeRamVirtualCompiler.body instruction := by
  cases instruction <;> simp [CoreInstruction, body] at hcore ⊢

theorem body_length_le (programLength pc : Nat) (instruction : Instr) :
    (body programLength pc instruction).length ≤ 16 := by
  cases instruction <;> simp [body, readBody, inputLoadBody, TapeRamVirtualCompiler.body,
    readCell, writeCell]

def paddedBody (programLength pc : Nat) (instruction : Instr) : Program :=
  body programLength pc instruction ++
    List.replicate (16 - (body programLength pc instruction).length) (.set 5 0)

theorem paddedBody_eq_of_core (programLength pc : Nat) (instruction : Instr)
    (hcore : CoreInstruction instruction) :
    paddedBody programLength pc instruction = TapeRamVirtualCompiler.paddedBody instruction := by
  simp [paddedBody, TapeRamVirtualCompiler.paddedBody,
    body_eq_of_core programLength pc instruction hcore]

@[simp] theorem paddedBody_length (programLength pc : Nat) (instruction : Instr) :
    (paddedBody programLength pc instruction).length = 16 := by
  simp only [paddedBody, List.length_append, List.length_replicate]
  have := body_length_le programLength pc instruction
  omega

def branch (pc : Nat) : Instr → Program
  | .halt => [.halt, .halt]
  | .jump target => [.jump (location target), .halt]
  | .jzero _ target | .jeof target =>
      [.jzero resultRegister (location target), .jump (location (pc + 1))]
  | _ => [.jump (location (pc + 1)), .halt]

def block (programLength pc : Nat) (instruction : Instr) : Program :=
  paddedBody programLength pc instruction ++ branch pc instruction

def blocks (programLength pc : Nat) : Program → Program
  | [] => []
  | instruction :: rest =>
      block programLength pc instruction ++ blocks programLength (pc + 1) rest

/-- This program uses only legacy instructions. The final halt also serves
as the target of a logical read from an exhausted snapshot. -/
def compile (extra : Nat) (program : Program) : Program :=
  prelude extra ++ blocks program.length 0 program ++ [.halt]

@[simp] theorem prelude_length (extra : Nat) : (prelude extra).length = 20 := by rfl

@[simp] theorem branch_length (pc : Nat) (instruction : Instr) :
    (branch pc instruction).length = 2 := by cases instruction <;> rfl

@[simp] theorem block_length (programLength pc : Nat) (instruction : Instr) :
    (block programLength pc instruction).length = 18 := by simp [block]

@[simp] theorem blocks_length (programLength pc : Nat) (program : Program) :
    (blocks programLength pc program).length = 18 * program.length := by
  induction program generalizing pc with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [blocks, List.length_append, block_length, ih, List.length_cons]
      omega

@[simp] theorem compile_length (extra : Nat) (program : Program) :
    (compile extra program).length = location program.length + 1 := by
  simp [compile, location, Nat.add_assoc]

theorem blocks_get (program : Program) (programLength base pc offset : Nat)
    (hoffset : offset < 18) :
    (blocks programLength base program)[18 * pc + offset]? =
      program[pc]?.bind (fun instruction =>
        (block programLength (base + pc) instruction)[offset]?) := by
  induction program generalizing base pc with
  | nil => simp [blocks]
  | cons instruction rest ih =>
      cases pc with
      | zero => simp [blocks, List.getElem?_append, hoffset]
      | succ pc =>
          have hlarge : ¬18 * (pc + 1) + offset < 18 := by omega
          simp only [blocks, List.getElem?_append, block_length, hlarge,
            ↓reduceIte, List.getElem?_cons_succ]
          rw [show 18 * (pc + 1) + offset - 18 = 18 * pc + offset by omega, ih]
          simp [Nat.add_comm, Nat.add_left_comm]

theorem compile_get (extra : Nat) (program : Program) (pc offset : Nat)
    (hpc : pc < program.length) (hoffset : offset < 18) :
    (compile extra program)[location pc + offset]? =
      program[pc]?.bind (fun instruction =>
        (block program.length pc instruction)[offset]?) := by
  have hprefix : location pc + offset < (prelude extra ++ blocks program.length 0 program).length := by
    simp only [List.length_append, prelude_length, blocks_length, location]
    omega
  have hlarge : ¬location pc + offset < (prelude extra).length := by
    simp only [prelude_length, location]
    omega
  simp only [compile, List.getElem?_append, hprefix, hlarge, ↓reduceIte]
  have hsub : location pc + offset - (prelude extra).length = 18 * pc + offset := by
    simp only [prelude_length, location]
    omega
  rw [hsub, blocks_get program program.length 0 pc offset hoffset, Nat.zero_add]

theorem compile_get_paddedBody (extra : Nat) (program : Program) (pc : Nat)
    (instruction : Instr) (hfetch : program[pc]? = some instruction)
    (offset : Nat) (hoffset : offset < 16) :
    (compile extra program)[location pc + offset]? =
      (paddedBody program.length pc instruction)[offset]? := by
  have hpc := (List.getElem?_eq_some_iff.mp hfetch).choose
  rw [compile_get extra program pc offset hpc (by omega), hfetch]
  simp [block, List.getElem?_append, hoffset]

theorem compile_get_branch (extra : Nat) (program : Program) (pc : Nat)
    (instruction : Instr) (hfetch : program[pc]? = some instruction)
    (offset : Nat) (hoffset : offset < 2) :
    (compile extra program)[location pc + 16 + offset]? =
      (branch pc instruction)[offset]? := by
  have hpc := (List.getElem?_eq_some_iff.mp hfetch).choose
  rw [show location pc + 16 + offset = location pc + (16 + offset) by omega,
    compile_get extra program pc (16 + offset) hpc (by omega), hfetch]
  simp [block, List.getElem?_append, hoffset]

@[simp] theorem compile_get_halt (extra : Nat) (program : Program) :
    (compile extra program)[location program.length]? = some .halt := by
  simp [compile, List.getElem?_append, location]

theorem compile_get_outside (extra : Nat) (program : Program) (pc : Nat)
    (hpc : program.length < pc) :
    (compile extra program)[location pc]? = none := by
  apply List.getElem?_eq_none
  simp only [compile_length, location]
  omega

end Lax759944Proofs.TapeRamBufferedCompiler
