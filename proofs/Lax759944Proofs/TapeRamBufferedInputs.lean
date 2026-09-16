import Lax759944Proofs.TapeRamBufferedState

namespace Lax759944Proofs.TapeRamBufferedInputs

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler TapeRamBufferedState

theorem large_capacity {v : Nat} {values : List Nat}
    (hcapacity : values.length + 32 < 2 ^ v) : 64 < 2 ^ (v + 1) := by
  rw [Nat.pow_succ]
  omega

/-- Complete the straight-line padding after an adapter body. -/
theorem pad_run {v extra cursor : Nat} {values : List Nat} {program : Program}
    {instruction : Instr} {source next : State} {before bodyScratch : Nat → Nat}
    (hcapacity : 16 ≤ 2 ^ (v + 1)) (hfetch : program[source.pc]? = some instruction)
    (hadapter : AdapterScratch v values cursor bodyScratch)
    (hready : BranchReady v instruction source bodyScratch)
    (hlinear : ∀ i ∈ body program.length source.pc instruction, StraightLine i)
    (hbody : execute (v + 1) (body program.length source.pc instruction)
      (state values (location source.pc) source.mem before [] source.out) =
        some (state values (location source.pc + (body program.length source.pc instruction).length)
          next.mem bodyScratch [] next.out)) :
    ∃ nextScratch,
      AdapterScratch v values cursor nextScratch ∧ BranchReady v instruction source nextScratch ∧
      run (v + 1) (compile extra program) 16
        (state values (location source.pc) source.mem before [] source.out) =
        some (state values (location source.pc + 16) next.mem nextScratch [] next.out) := by
  rcases padding_execute v (16 - (body program.length source.pc instruction).length)
      (location source.pc + (body program.length source.pc instruction).length)
      next.mem bodyScratch [] next.out hcapacity hadapter.compiler with
    ⟨nextScratch, hcompiler, hfive, hhigh, hpadding⟩
  refine ⟨nextScratch, hadapter.preserve hcompiler hhigh, ?_, ?_⟩
  · cases instruction <;> simp only [BranchReady] at hready ⊢
    all_goals try trivial
    all_goals rw [hfive]; exact hready
  · have hall : ∀ i ∈ paddedBody program.length source.pc instruction, StraightLine i := by
      intro i hi
      simp only [paddedBody, List.mem_append, List.mem_replicate] at hi
      rcases hi with hi | ⟨_, rfl⟩
      · exact hlinear i hi
      · trivial
    have hprefix : ∀ k, k < (paddedBody program.length source.pc instruction).length →
        (compile extra program)[(state values (location source.pc) source.mem before [] source.out).pc + k]? =
          (paddedBody program.length source.pc instruction)[k]? := by
      intro k hk
      exact compile_get_paddedBody extra program source.pc instruction hfetch k (by simpa using hk)
    rw [show 16 = (paddedBody program.length source.pc instruction).length by simp,
      run_eq_execute _ _ _ _ hall hprefix, paddedBody, execute_append, hbody,
      Option.bind_some, hpadding]
    congr 2
    simp only [List.length_append, List.length_replicate]
    have := body_length_le program.length source.pc instruction
    omega

theorem inputLength_body {v pc cursor programLength address : Nat} {values : List Nat}
    {memory scratch : Nat → Nat} {output : List Nat}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hscratch : AdapterScratch v values cursor scratch) :
    ∃ nextScratch,
      AdapterScratch v values cursor nextScratch ∧
      execute (v + 1) (body programLength pc (.inputLength address))
        (state values pc memory scratch [] output) =
        some (state values (pc + 6) (setCell v memory address values.length)
          nextScratch [] output) := by
  have hlarge := large_capacity hcapacity
  rcases TapeRamVirtualSimulation.body_set (original := values) v pc address values.length
      memory scratch [] output (by omega) hscratch.compiler with
    ⟨nextScratch, hcompiler, hhigh, hbody⟩
  refine ⟨nextScratch, hscratch.preserve hcompiler hhigh, ?_⟩
  have h13 : 13 % 2 ^ (v + 1) = 13 := Nat.mod_eq_of_lt (by omega)
  have h25 : 25 % 2 ^ (v + 1) = 25 := Nat.mod_eq_of_lt (by omega)
  have hlength : merge memory scratch 13 = values.length := by
    simpa only [hscratch.length_eq] using merge_odd memory scratch 6
  have hzero : merge memory scratch 25 = 0 := by
    simpa only [hscratch.zero_eq] using merge_odd memory scratch 12
  have hlen : (TapeRamVirtualCompiler.body (.set address values.length)).length = 6 := rfl
  rw [hlen] at hbody
  simpa only [body, TapeRamVirtualCompiler.body, List.singleton_append, execute,
    Instr.effect, state, lengthRegister, zeroRegister, TapeRamVirtualCompiler.resultRegister,
    h13, h25, hlength, hzero, Nat.add_zero] using hbody

theorem inputLength_run {v extra cursor address : Nat} {values : List Nat} {program : Program}
    {source : State} {scratch : Nat → Nat}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hfetch : program[source.pc]? = some (.inputLength address))
    (hscratch : AdapterScratch v values cursor scratch) :
    ∃ nextScratch,
      AdapterScratch v values cursor nextScratch ∧
      run (v + 1) (compile extra program) 16
        (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16)
          (setCell v source.mem address values.length) nextScratch [] source.out) := by
  rcases inputLength_body (pc := location source.pc) (programLength := program.length)
      (address := address) (memory := source.mem) (output := source.out) hcapacity hscratch with
    ⟨bodyScratch, hadapter, hbody⟩
  let next : State := { source with mem := setCell v source.mem address values.length }
  have hlarge := large_capacity hcapacity
  rcases pad_run (extra := extra) (next := next) (by omega) hfetch hadapter
      (by trivial) (by simp [body, TapeRamVirtualCompiler.writeCell, StraightLine])
      (by simpa [next, body, TapeRamVirtualCompiler.writeCell] using hbody) with
    ⟨nextScratch, hnext, _, hrun⟩
  exact ⟨nextScratch, hnext, hrun⟩

theorem jeof_run {v extra cursor target : Nat} {values : List Nat} {program : Program}
    {source : State} {scratch : Nat → Nat}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hfetch : program[source.pc]? = some (.jeof target))
    (hinput : source.inp = values.drop cursor)
    (hscratch : AdapterScratch v values cursor scratch) :
    ∃ nextScratch,
      AdapterScratch v values cursor nextScratch ∧
      BranchReady v (.jeof target) source nextScratch ∧
      run (v + 1) (compile extra program) 16
        (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16) source.mem nextScratch [] source.out) := by
  have hlarge := large_capacity hcapacity
  have hgap : values.length - cursor < 2 ^ (v + 1) := by
    have := length_lt hcapacity
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show v ≤ v + 1 by omega)
    omega
  let after := put scratch 5 (values.length - cursor)
  have hafter : AdapterScratch v values cursor after := hscratch.preserve
    (compilerScratch_put v scratch hscratch.compiler 5 _ (by omega))
    (scratchPreservedFrom_put 6 scratch 5 _ (by omega))
  have hready : BranchReady v (.jeof target) source after := by
    simp [BranchReady, after, hinput, Nat.sub_eq_zero_iff_le, List.drop_eq_nil_iff]
  have hbody : execute (v + 1) (body program.length source.pc (.jeof target))
      (state values (location source.pc) source.mem scratch [] source.out) =
      some (state values (location source.pc + 1) source.mem after [] source.out) := by
    simpa only [body, TapeRamVirtualCompiler.resultRegister, lengthRegister,
      cursorRegister, BinaryKind.instruction, BinaryKind.value, hscratch.length_eq,
      hscratch.cursor_eq, Nat.mod_eq_of_lt hgap] using
      (binaryRegister_execute (original := values) .sub v (location source.pc) 5 6 7
        source.mem scratch [] source.out (by omega) (by omega) (by omega))
  exact pad_run (extra := extra) (next := source) (by omega) hfetch hafter hready
    (by simp [body, StraightLine]) (by simpa [body] using hbody)

end Lax759944Proofs.TapeRamBufferedInputs
