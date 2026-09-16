import Lax759944Proofs.TapeRamBufferedInputs

namespace Lax759944Proofs.TapeRamBufferedRead

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler TapeRamBufferedState TapeRamBufferedInputs

theorem run_one_of_execute {w : Nat} {program : Program} {instruction : Instr}
    {source next : State} (hfetch : program[source.pc]? = some instruction)
    (heffect : execute w [instruction] source = some next) :
    run w program 1 source = some next := by
  simpa only [run, step, hfetch, Option.bind_some, execute, Option.bind_fun_some] using heffect

/-- Six instructions find the next snapshot word and advance the logical cursor. -/
theorem read_prefix {v extra cursor address : Nat} {values : List Nat} {program : Program}
    {pc : Nat} {memory scratch : Nat → Nat} {output : List Nat}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hfit : ∀ value ∈ values, value < 2 ^ v)
    (hfetch : program[pc]? = some (.read address))
    (hscratch : AdapterScratch v values cursor scratch) (hcursor : cursor < values.length) :
    ∃ nextScratch,
      AdapterScratch v values (cursor + 1) nextScratch ∧
      nextScratch 5 = values[cursor]'hcursor ∧
      run (v + 1) (compile extra program) 6
        (state values (location pc) memory scratch [] output) =
        some (state values (location pc + 6) memory nextScratch [] output) := by
  let gap := values.length - cursor
  let value := values[cursor]'hcursor
  let s1 := put scratch 5 gap
  let s3 := put s1 2 (2 * cursor)
  let s4 := put s3 2 (65 + 2 * cursor)
  let s5 := put s4 5 value
  let s6 := put s5 7 (cursor + 1)
  have hlarge := large_capacity hcapacity
  have hgap : gap < 2 ^ (v + 1) := by
    dsimp [gap]
    have := length_lt hcapacity
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show v ≤ v + 1 by omega)
    omega
  have hgapZero : gap ≠ 0 := by dsimp [gap]; omega
  have hdouble : 2 * cursor < 2 ^ (v + 1) := by rw [Nat.pow_succ]; omega
  have haddress := buffer_address_lt hcapacity hcursor
  have hsum : 2 * cursor + 65 < 2 ^ (v + 1) := by omega
  have hnextCursor : cursor + 1 < 2 ^ (v + 1) := by
    have := length_lt hcapacity
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show v ≤ v + 1 by omega)
    omega
  have hvalue : value < 2 ^ v := hfit value (List.getElem_mem hcursor)
  have hvaluePhysical : value < 2 ^ (v + 1) :=
    hvalue.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have h13 : 13 % 2 ^ (v + 1) = 13 := Nat.mod_eq_of_lt (by omega)
  have h15 : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
  have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
  have h5 : 5 % 2 ^ (v + 1) = 5 := Nat.mod_eq_of_lt (by omega)
  have hf0 : (compile extra program)[location pc + 0]? = some (.sub 11 13 15) := by
    simpa [paddedBody, body, readBody, TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister, lengthRegister, cursorRegister,
      baseRegister, oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 0 (by omega)
  have hf1 : (compile extra program)[location pc + 1]? = some (.jzero 11 (location program.length)) := by
    simpa [paddedBody, body, readBody, TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister, lengthRegister, cursorRegister,
      baseRegister, oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 1 (by omega)
  have hf2 : (compile extra program)[location pc + 2]? = some (.mul 5 15 3) := by
    simpa [paddedBody, body, readBody, TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister, lengthRegister, cursorRegister,
      baseRegister, oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 2 (by omega)
  have hf3 : (compile extra program)[location pc + 3]? = some (.add 5 5 21) := by
    simpa [paddedBody, body, readBody, TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister, lengthRegister, cursorRegister,
      baseRegister, oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 3 (by omega)
  have hf4 : (compile extra program)[location pc + 4]? = some (.load 11 5) := by
    simpa [paddedBody, body, readBody, TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister, lengthRegister, cursorRegister,
      baseRegister, oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 4 (by omega)
  have hf5 : (compile extra program)[location pc + 5]? = some (.add 15 15 23) := by
    simpa [paddedBody, body, readBody, TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister,
      TapeRamVirtualCompiler.twoRegister, lengthRegister, cursorRegister,
      baseRegister, oneRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 5 (by omega)
  have h0 : execute (v + 1) [.sub 11 13 15]
      (state values (location pc) memory scratch [] output) =
      some (state values (location pc + 1) memory s1 [] output) := by
    have hsub := binaryRegister_execute (original := values) .sub v (location pc) 5 6 7
      memory scratch [] output (by omega) (by omega) (by omega)
    simp only [BinaryKind.instruction, BinaryKind.value, hscratch.length_eq,
      hscratch.cursor_eq] at hsub
    rw [Nat.mod_eq_of_lt (show values.length - cursor < 2 ^ (v + 1) from hgap)] at hsub
    exact hsub
  have h1 : execute (v + 1) [.jzero 11 (location program.length)]
      (state values (location pc + 1) memory s1 [] output) =
      some (state values (location pc + 2) memory s1 [] output) := by
    have hread : merge memory s1 11 = gap := by simpa [s1] using merge_odd memory s1 5
    simp [execute, Instr.effect, state, h11, hread, hgapZero]
  have h2 : execute (v + 1) [.mul 5 15 3]
      (state values (location pc + 2) memory s1 [] output) =
      some (state values (location pc + 3) memory s3 [] output) := by
    have hmul := binaryRegister_execute (original := values) .mul v (location pc + 2) 2 7 1
      memory s1 [] output (by omega) (by omega) (by omega)
    simp only [BinaryKind.instruction, BinaryKind.value] at hmul
    rw [show s1 7 = cursor by simp [s1, put, hscratch.cursor_eq],
      show s1 1 = 2 by simp [s1, put, hscratch.compiler.2],
      Nat.mul_comm cursor 2, Nat.mod_eq_of_lt hdouble] at hmul
    exact hmul
  have h3 : execute (v + 1) [.add 5 5 21]
      (state values (location pc + 3) memory s3 [] output) =
      some (state values (location pc + 4) memory s4 [] output) := by
    have hadd := binaryRegister_execute (original := values) .add v (location pc + 3) 2 2 10
      memory s3 [] output (by omega) (by omega) (by omega)
    simp only [BinaryKind.instruction, BinaryKind.value] at hadd
    rw [show s3 2 = 2 * cursor by simp [s3],
      show s3 10 = 65 by simp [s3, s1, put, hscratch.base_eq],
      Nat.mod_eq_of_lt hsum, Nat.add_comm (2 * cursor) 65] at hadd
    exact hadd
  have h4 : execute (v + 1) [.load 11 5]
      (state values (location pc + 4) memory s4 [] output) =
      some (state values (location pc + 5) memory s5 [] output) := by
    have hpointer : merge memory s4 5 = 65 + 2 * cursor := by
      simpa [s4] using merge_odd memory s4 2
    have hbuffer : merge memory s4 (65 + 2 * cursor) = value := by
      rw [show 65 + 2 * cursor = 2 * (bufferBase + cursor) + 1 by simp [bufferBase]; omega,
        merge_odd]
      simpa [s4, s3, s1, put, bufferBase, value,
        show 32 + cursor ≠ 2 by omega, show 32 + cursor ≠ 5 by omega] using
        hscratch.buffer cursor hcursor
    have hset := set_odd v memory s4 11 value (by decide) (by omega)
    simp only [execute, Instr.effect, state, h5, hpointer,
      Nat.mod_eq_of_lt haddress, hbuffer, hset, Option.bind_some]
    simpa [s5, Nat.mod_eq_of_lt hvaluePhysical]
  have h5run : execute (v + 1) [.add 15 15 23]
      (state values (location pc + 5) memory s5 [] output) =
      some (state values (location pc + 6) memory s6 [] output) := by
    simpa [BinaryKind.instruction, BinaryKind.value, s1, s3, s4, s5, s6, put,
      hscratch.cursor_eq, hscratch.one_eq, Nat.mod_eq_of_lt hnextCursor] using
      (binaryRegister_execute (original := values) .add v (location pc + 5) 7 7 11
        memory s5 [] output (by omega) (by omega) (by omega))
  have hsix : AdapterScratch v values (cursor + 1) s6 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩
    · constructor <;> simp [s6, s5, s4, s3, s1, put, hscratch.compiler.1, hscratch.compiler.2]
    · simp [s6, s5, s4, s3, s1, put, hscratch.length_eq]
    · simp [s6, put]
    · simp [s6, s5, s4, s3, s1, put, hscratch.base_eq]
    · simp [s6, s5, s4, s3, s1, put, hscratch.one_eq]
    · simp [s6, s5, s4, s3, s1, put, hscratch.zero_eq]
    · apply hscratch.buffer.preserve
      intro index hindex
      simp [s6, s5, s4, s3, s1, put, show index ≠ 7 by omega,
        show index ≠ 5 by omega, show index ≠ 2 by omega]
  refine ⟨s6, hsix, by simp [s6, s5, put, value], ?_⟩
  have hr0 := run_one_of_execute (by simpa only [state, Nat.add_zero] using hf0) h0
  have hr1 := run_one_of_execute (by simpa only [state] using hf1) h1
  have hr2 := run_one_of_execute (by simpa only [state] using hf2) h2
  have hr3 := run_one_of_execute (by simpa only [state] using hf3) h3
  have hr4 := run_one_of_execute (by simpa only [state] using hf4) h4
  have hr5 := run_one_of_execute (by simpa only [state] using hf5) h5run
  rw [show 6 = 1 + (1 + (1 + (1 + (1 + 1)))) by decide,
    run_add, hr0, Option.bind_some, run_add, hr1, Option.bind_some,
    run_add, hr2, Option.bind_some, run_add, hr3, Option.bind_some,
    run_add, hr4, Option.bind_some, hr5]

theorem read_run {v extra cursor address : Nat} {values : List Nat} {program : Program}
    {pc : Nat} {memory scratch : Nat → Nat} {output : List Nat}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hfit : ∀ value ∈ values, value < 2 ^ v)
    (hfetch : program[pc]? = some (.read address))
    (hscratch : AdapterScratch v values cursor scratch) (hcursor : cursor < values.length) :
    ∃ nextScratch,
      AdapterScratch v values (cursor + 1) nextScratch ∧
      run (v + 1) (compile extra program) 16
        (state values (location pc) memory scratch [] output) =
        some (state values (location pc + 16)
          (setCell v memory address (values[cursor]'hcursor)) nextScratch [] output) := by
  rcases read_prefix (extra := extra) (memory := memory) (output := output) hcapacity hfit hfetch hscratch hcursor with
    ⟨prefixScratch, hprefixAdapter, hvalue, hprefixRun⟩
  let value := values[cursor]'hcursor
  let afterWrite := put (put prefixScratch 2 (2 * (address % 2 ^ v))) 5 value
  have hword : value < 2 ^ v := hfit value (List.getElem_mem hcursor)
  have hlarge := large_capacity hcapacity
  have hwriteCompiler : CompilerScratch v afterWrite := compilerScratch_put v _
    (compilerScratch_put v prefixScratch hprefixAdapter.compiler 2 _ (by omega)) 5 _ (by omega)
  have hwriteAdapter : AdapterScratch v values (cursor + 1) afterWrite :=
    hprefixAdapter.preserve hwriteCompiler (by
      intro index hindex
      simp [afterWrite, put, show index ≠ 2 by omega, show index ≠ 5 by omega])
  rcases padding_execute (original := values) v 5 (location pc + 11)
      (setCell v memory address value) afterWrite [] output (by omega) hwriteCompiler with
    ⟨nextScratch, hnextCompiler, _, hnextHigh, hpadding⟩
  refine ⟨nextScratch, hwriteAdapter.preserve hnextCompiler hnextHigh, ?_⟩
  let suffix : Program := TapeRamVirtualCompiler.writeCell address ++ List.replicate 5 (.set 5 0)
  let prefixCode : Program :=
    [.sub 11 13 15, .jzero 11 (location program.length), .mul 5 15 3,
      .add 5 5 21, .load 11 5, .add 15 15 23]
  have hdecomp : paddedBody program.length pc (.read address) = prefixCode ++ suffix := by rfl
  have hprefixLength : prefixCode.length = 6 := rfl
  have hsuffixLength : suffix.length = 10 := rfl
  have hlinear : ∀ i ∈ suffix, StraightLine i := by
    simp [suffix, TapeRamVirtualCompiler.writeCell, StraightLine]
  have hsuffixFetch : ∀ k, k < suffix.length →
      (compile extra program)[(state values (location pc + 6) memory prefixScratch [] output).pc + k]? =
        suffix[k]? := by
    intro k hk
    change (compile extra program)[location pc + 6 + k]? = _
    rw [show location pc + 6 + k = location pc + (6 + k) by omega,
      compile_get_paddedBody extra program pc (.read address) hfetch (6 + k)
        (by rw [hsuffixLength] at hk; omega), hdecomp]
    simp [List.getElem?_append, hprefixLength, show ¬6 + k < 6 by omega]
  have hsuffixExecute : execute (v + 1) suffix
      (state values (location pc + 6) memory prefixScratch [] output) =
      some (state values (location pc + 16) (setCell v memory address value) nextScratch [] output) := by
    simp only [suffix]
    rw [execute_append, writeCell_execute v (location pc + 6) address
      memory prefixScratch [] output (by omega) hprefixAdapter.compiler.1 hprefixAdapter.compiler.2]
    simp only [Option.bind_some, hvalue,
      Nat.mod_eq_of_lt (show values[cursor] < 2 ^ v from hword)]
    exact hpadding
  have hsuffixRun : run (v + 1) (compile extra program) 10
      (state values (location pc + 6) memory prefixScratch [] output) =
      some (state values (location pc + 16) (setCell v memory address value) nextScratch [] output) := by
    rw [← hsuffixLength, run_eq_execute _ _ _ _ hlinear hsuffixFetch]
    exact hsuffixExecute
  rw [show 16 = 6 + 10 by decide, run_add, hprefixRun, Option.bind_some, hsuffixRun]

/-- A read past the snapshot branches to the shared terminal instruction. -/
theorem read_exhausted {v extra address : Nat} {values : List Nat} {program : Program}
    {pc : Nat} {memory scratch : Nat → Nat} {output : List Nat}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hfetch : program[pc]? = some (.read address))
    (hscratch : AdapterScratch v values values.length scratch) :
    ∃ final,
      run (v + 1) (compile extra program) 2
        (state values (location pc) memory scratch [] output) = some final ∧
      step (v + 1) (compile extra program) final = none ∧ final.out = output := by
  have hlarge := large_capacity hcapacity
  let after := put scratch 5 0
  have hsub : execute (v + 1) [.sub 11 13 15]
      (state values (location pc) memory scratch [] output) =
      some (state values (location pc + 1) memory after [] output) := by
    simpa [BinaryKind.instruction, BinaryKind.value, hscratch.length_eq, hscratch.cursor_eq, after] using
      (binaryRegister_execute (original := values) .sub v (location pc) 5 6 7
        memory scratch [] output (by omega) (by omega) (by omega))
  have hbranch : execute (v + 1) [.jzero 11 (location program.length)]
      (state values (location pc + 1) memory after [] output) =
      some (state values (location program.length) memory after [] output) := by
    have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
    have hzero : merge memory after 11 = 0 := by simpa [after] using merge_odd memory after 5
    simp [execute, Instr.effect, state, h11, hzero]
  have hf0 : (compile extra program)[location pc]? = some (.sub 11 13 15) := by
    simpa [paddedBody, body, readBody, TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister, lengthRegister, cursorRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 0 (by omega)
  have hf1 : (compile extra program)[location pc + 1]? =
      some (.jzero 11 (location program.length)) := by
    simpa [paddedBody, body, readBody, TapeRamVirtualCompiler.writeCell,
      TapeRamVirtualCompiler.resultRegister] using
      compile_get_paddedBody extra program pc (.read address) hfetch 1 (by omega)
  refine ⟨state values (location program.length) memory after [] output, ?_, ?_, rfl⟩
  · have hr0 := run_one_of_execute (by simpa only [state] using hf0) hsub
    have hr1 := run_one_of_execute (by simpa only [state] using hf1) hbranch
    rw [show 2 = 1 + 1 by decide, run_add, hr0, Option.bind_some, hr1]
  · simp only [step, state, compile_get_halt, Option.bind_some, Instr.effect]

end Lax759944Proofs.TapeRamBufferedRead
