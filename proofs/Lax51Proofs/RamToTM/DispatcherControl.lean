import Lax51Proofs.RamToTM.SparseBitMacros

namespace Lax51Proofs.RamToTM

open Lax51Proofs.Microcode

/-! Finite control used by the RAM interpreter.  For a fixed program all
in-range program counters are finite; every out-of-range counter has the same
observable behavior (instruction fetch fails), so they share one sentinel. -/

abbrev BoundedPC (p : Program) := Fin (p.length + 1)

instance (p : Program) : Inhabited (BoundedPC p) := ⟨0, by omega⟩

def boundPC (p : Program) (pc : ℕ) : BoundedPC p :=
  if h : pc < p.length then ⟨pc, by omega⟩ else ⟨p.length, by omega⟩

def BoundedPC.isSentinel {p : Program} (pc : BoundedPC p) : Bool :=
  decide (pc.val = p.length)

def BoundedPC.fetch {p : Program} (pc : BoundedPC p) : Option Instr :=
  if pc.val < p.length then p[pc.val]? else none

@[simp] theorem boundPC_val_of_lt {p : Program} {pc : ℕ} (h : pc < p.length) :
    (boundPC p pc).val = pc := by
  simp [boundPC, h]

@[simp] theorem boundPC_val_of_not_lt {p : Program} {pc : ℕ}
    (h : ¬ pc < p.length) : (boundPC p pc).val = p.length := by
  simp [boundPC, h]

theorem boundPC_eq_sentinel_iff (p : Program) (pc : ℕ) :
    (boundPC p pc).val = p.length ↔ ¬ pc < p.length := by
  by_cases h : pc < p.length
  · simp [boundPC, h, Nat.ne_of_lt h]
  · simp [boundPC, h]

@[simp] theorem fetch_boundPC (p : Program) (pc : ℕ) :
    (boundPC p pc).fetch = p[pc]? := by
  by_cases h : pc < p.length
  · simp [BoundedPC.fetch, boundPC, h]
  · have hout : p[pc]? = none := List.getElem?_eq_none (by omega)
    simp [BoundedPC.fetch, boundPC, h, hout]

def nextPC (p : Program) (pc : BoundedPC p) : BoundedPC p :=
  boundPC p (pc.val + 1)

def jumpPC (p : Program) (target : ℕ) : BoundedPC p :=
  boundPC p target

theorem nextPC_boundPC_of_lt {p : Program} {pc : ℕ} (h : pc < p.length) :
    nextPC p (boundPC p pc) = boundPC p (pc + 1) := by
  apply Fin.ext
  simp [nextPC, h]

@[simp] theorem jumpPC_val_of_lt {p : Program} {target : ℕ}
    (h : target < p.length) : (jumpPC p target).val = target := by
  simp [jumpPC, h]

/-- The finite dispatcher only needs the constructor class in its dynamic
control; operands and jump targets are recovered from the fixed program table. -/
inductive InstrClass
  | read | write | load | store | storeInd
  | add | sub | mul | div | and | or | xor | compl | shiftl | shiftr
  | jump | jzero | jgtz | halt
  deriving DecidableEq, Fintype, Inhabited

def instrClass : Instr → InstrClass
  | .read _ => .read
  | .write _ => .write
  | .load _ => .load
  | .store _ => .store
  | .storeInd _ => .storeInd
  | .add _ => .add
  | .sub _ => .sub
  | .mul _ => .mul
  | .div _ => .div
  | .and _ => .and
  | .or _ => .or
  | .xor _ => .xor
  | .compl _ => .compl
  | .shiftl _ => .shiftl
  | .shiftr _ => .shiftr
  | .jump _ => .jump
  | .jzero _ => .jzero
  | .jgtz _ => .jgtz
  | .halt => .halt

@[simp] theorem instrClass_eq_halt_iff (i : Instr) :
    instrClass i = InstrClass.halt ↔ i = Instr.halt := by
  cases i <;> simp [instrClass]

/-- The control location at which the next RAM instruction is fetched. -/
inductive DispatchLabel (p : Program)
  | fetch (pc : BoundedPC p)
  | stopped
  deriving DecidableEq, Fintype, Inhabited

def initialDispatchLabel (p : Program) : DispatchLabel p :=
  .fetch (boundPC p 0)

def DispatchLabel.instruction {p : Program} : DispatchLabel p → Option Instr
  | .fetch pc => pc.fetch
  | .stopped => none

@[simp] theorem initialDispatchLabel_instruction (p : Program) :
    (initialDispatchLabel p).instruction = p[0]? := by
  simp [initialDispatchLabel, DispatchLabel.instruction]

def stateDispatchLabel (p : Program) (s : SparseState) : DispatchLabel p :=
  .fetch (boundPC p s.pc)

@[simp] theorem stateDispatchLabel_instruction (p : Program) (s : SparseState) :
    (stateDispatchLabel p s).instruction = p[s.pc]? := by
  simp [stateDispatchLabel, DispatchLabel.instruction]

def dispatchSuccessor (p : Program) (pc : BoundedPC p) (i : Instr)
    (acc : ℕ) : DispatchLabel p :=
  match i with
  | .jump target => .fetch (jumpPC p target)
  | .jzero target =>
      .fetch (if acc = 0 then jumpPC p target else nextPC p pc)
  | .jgtz target =>
      .fetch (if 0 < acc then jumpPC p target else nextPC p pc)
  | .halt => .stopped
  | _ => .fetch (nextPC p pc)

theorem fetch_some_pc_lt {p : Program} {pc : ℕ} {i : Instr}
    (h : p[pc]? = some i) : pc < p.length := by
  by_contra hn
  rw [List.getElem?_eq_none (by omega)] at h
  contradiction

/-- Control-flow half of the one-instruction simulation theorem. -/
theorem dispatchSuccessor_correct {p : Program} {w : ℕ} {i : Instr}
    {s s' : SparseState} (hfetch : p[s.pc]? = some i)
    (heffect : sparseEffect w i s = some s') :
    dispatchSuccessor p (boundPC p s.pc) i s.acc = stateDispatchLabel p s' := by
  have hpc : s.pc < p.length := fetch_some_pc_lt hfetch
  cases i with
  | read address =>
      cases hin : s.inp with
      | nil => simp [sparseEffect, hin] at heffect
      | cons value input =>
          simp [sparseEffect, hin] at heffect
          subst s'
          simp [dispatchSuccessor, stateDispatchLabel,
            nextPC_boundPC_of_lt hpc]
  | write operand =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | load operand =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | store address =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | storeInd address =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | add operand =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | sub operand =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | mul operand =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | div operand =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | and operand =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | or operand =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | xor operand | compl operand =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | shiftl operand =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel, nextPC_boundPC_of_lt hpc]
  | shiftr operand =>
      simp [sparseEffect] at heffect
      subst s'
      simp [dispatchSuccessor, stateDispatchLabel,
        nextPC_boundPC_of_lt hpc]
  | jump target =>
      simp [sparseEffect] at heffect
      subst s'
      rfl
  | jzero target =>
      simp [sparseEffect] at heffect
      subst s'
      by_cases hz : s.acc = 0
      · simp [dispatchSuccessor, stateDispatchLabel, jumpPC, hz]
      · simp [dispatchSuccessor, stateDispatchLabel, hz,
          nextPC_boundPC_of_lt hpc]
  | jgtz target =>
      simp [sparseEffect] at heffect
      subst s'
      by_cases hp : 0 < s.acc
      · simp [dispatchSuccessor, stateDispatchLabel, jumpPC, hp]
      · simp [dispatchSuccessor, stateDispatchLabel, hp,
          nextPC_boundPC_of_lt hpc]
  | halt => simp [sparseEffect] at heffect

end Lax51Proofs.RamToTM
