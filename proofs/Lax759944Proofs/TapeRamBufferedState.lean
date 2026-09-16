import Lax759944Proofs.TapeRamBufferedCompiler
import Mathlib.Data.List.TakeDrop

namespace Lax759944Proofs.TapeRamBufferedState

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler

/-- Every original input word is retained in the protected odd-addressed snapshot. -/
def BufferStored (values : List Nat) (scratch : Nat → Nat) : Prop :=
  ∀ (index : Nat) (hindex : index < values.length),
    scratch (bufferBase + index) = values[index]'hindex

structure AdapterScratch (v : Nat) (values : List Nat) (cursor : Nat)
    (scratch : Nat → Nat) : Prop where
  compiler : CompilerScratch v scratch
  length_eq : scratch 6 = values.length
  cursor_eq : scratch 7 = cursor
  base_eq : scratch 10 = 65
  one_eq : scratch 11 = 1
  zero_eq : scratch 12 = 0
  cursor_le : cursor ≤ values.length
  buffer : BufferStored values scratch

theorem BufferStored.preserve {values : List Nat} {before after : Nat → Nat}
    (hbefore : BufferStored values before)
    (hhigh : ScratchPreservedFrom 32 before after) : BufferStored values after := by
  intro index hindex
  rw [hhigh (bufferBase + index) (by simp [bufferBase])]
  exact hbefore index hindex

theorem AdapterScratch.preserve {v : Nat} {values : List Nat} {cursor : Nat}
    {before after : Nat → Nat} (hbefore : AdapterScratch v values cursor before)
    (hcompiler : CompilerScratch v after)
    (hhigh : ScratchPreservedFrom 6 before after) : AdapterScratch v values cursor after := by
  refine ⟨hcompiler, ?_, ?_, ?_, ?_, ?_, hbefore.cursor_le, ?_⟩
  · rw [hhigh 6 (by omega)]; exact hbefore.length_eq
  · rw [hhigh 7 (by omega)]; exact hbefore.cursor_eq
  · rw [hhigh 10 (by omega)]; exact hbefore.base_eq
  · rw [hhigh 11 (by omega)]; exact hbefore.one_eq
  · rw [hhigh 12 (by omega)]; exact hbefore.zero_eq
  · apply hbefore.buffer.preserve
    intro index hindex
    exact hhigh index (by omega)

theorem buffer_address_lt {v : Nat} {values : List Nat} {index : Nat}
    (hcapacity : values.length + 32 < 2 ^ v) (hindex : index < values.length) :
    65 + 2 * index < 2 ^ (v + 1) := by
  rw [Nat.pow_succ]
  omega

theorem length_lt {v : Nat} {values : List Nat}
    (hcapacity : values.length + 32 < 2 ^ v) : values.length < 2 ^ v := by omega

/-- Branch data comes from a virtual memory cell or the logical EOF test. -/
def BranchReady (v : Nat) (instruction : Instr) (source : State)
    (scratch : Nat → Nat) : Prop :=
  match instruction with
  | .jzero address _ => scratch 5 = source.mem (address % 2 ^ v)
  | .jeof _ => (scratch 5 = 0 ↔ source.inp = [])
  | _ => True

def Simulates (v : Nat) (values : List Nat) (source physical : State) : Prop :=
  ∃ cursor scratch,
    source.input = values ∧ source.inp = values.drop cursor ∧
    Normalized v source.mem ∧ AdapterScratch v values cursor scratch ∧
    physical = state values (location source.pc) source.mem scratch [] source.out

end Lax759944Proofs.TapeRamBufferedState
