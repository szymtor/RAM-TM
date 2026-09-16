import Lax759944Proofs.TapeRamBufferedCompiler
import Lax759944Proofs.LegacyRamProjection

namespace Lax759944Proofs.TapeRamBufferedLegacy

open Lax808846.Ram LegacyRamProjection TapeRamBufferedCompiler

theorem prelude_isLegacy (extra : Nat) :
    ∀ i ∈ prelude extra, IsLegacy i := by
  simp [prelude, TapeRamVirtualCompiler.prelude, IsLegacy]

theorem body_isLegacy (programLength pc : Nat) (instruction : Instr) :
    ∀ i ∈ body programLength pc instruction, IsLegacy i := by
  cases instruction <;>
    simp [body, readBody, inputLoadBody, TapeRamVirtualCompiler.body,
      TapeRamVirtualCompiler.readCell, TapeRamVirtualCompiler.writeCell, IsLegacy]

theorem paddedBody_isLegacy (programLength pc : Nat) (instruction : Instr) :
    ∀ i ∈ paddedBody programLength pc instruction, IsLegacy i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact body_isLegacy programLength pc instruction i hi
  · have heq := (List.mem_replicate.mp hi).2
    subst i
    trivial

theorem branch_isLegacy (pc : Nat) (instruction : Instr) :
    ∀ i ∈ branch pc instruction, IsLegacy i := by
  cases instruction <;> simp [branch, IsLegacy]

theorem blocks_isLegacy (programLength pc : Nat) (program : Program) :
    ∀ i ∈ blocks programLength pc program, IsLegacy i := by
  induction program generalizing pc with
  | nil => simp [blocks]
  | cons instruction rest ih =>
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · rcases List.mem_append.mp hi with hi | hi
        · exact paddedBody_isLegacy programLength pc instruction i hi
        · exact branch_isLegacy pc instruction i hi
      · exact ih (pc + 1) i hi

/-- The buffer compiler eliminates all extended input instructions. -/
theorem compile_isLegacy (extra : Nat) (program : Program) :
    ∀ i ∈ compile extra program, IsLegacy i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact prelude_isLegacy extra i hi
    · exact blocks_isLegacy program.length 0 program i hi
  · have heq : i = .halt := by simpa using hi
    subst i
    trivial

/-- The internal program implementing the buffered extended RAM. -/
def lower (extra : Nat) (program : Program) : Legacy.Ram.Program :=
  eraseProgram (compile extra program)

theorem embed_lower (extra : Nat) (program : Program) :
    LegacyRamBridge.embedProgram (lower extra program) = compile extra program :=
  embed_erase_program (compile_isLegacy extra program)

theorem runsTo_lower {extra w t : Nat} {program : Program} {input output : List Nat}
    (h : RunsTo w (compile extra program) input output t) :
    ∃ k ≤ t, Legacy.Ram.RunsTo w (lower extra program) input output k :=
  runsTo_erase (compile_isLegacy extra program) h

end Lax759944Proofs.TapeRamBufferedLegacy
