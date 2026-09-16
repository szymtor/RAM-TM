import Lax759944Proofs.TapeRamBufferedState
import Mathlib.Tactic.IntervalCases

namespace Lax759944Proofs.TapeRamBufferedIndexed

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler TapeRamBufferedState

private theorem put_low {v cursor : Nat} {values : List Nat} {scratch : Nat → Nat}
    (h : AdapterScratch v values cursor scratch) (i value : Nat)
    (hi : 2 ≤ i) (hi' : i < 6) : AdapterScratch v values cursor (put scratch i value) :=
  h.preserve (compilerScratch_put v scratch h.compiler i value hi)
    (scratchPreservedFrom_put 6 scratch i value hi')

private theorem put_temporary {v cursor : Nat} {values : List Nat} {scratch : Nat → Nat}
    (h : AdapterScratch v values cursor scratch) (value : Nat) :
    AdapterScratch v values cursor (put scratch 9 value) := by
  refine ⟨compilerScratch_put v scratch h.compiler 9 value (by omega),
    ?_, ?_, ?_, ?_, ?_, h.cursor_le, ?_⟩
  · simpa using h.length_eq
  · simpa using h.cursor_eq
  · simpa using h.base_eq
  · simpa using h.one_eq
  · simpa using h.zero_eq
  · exact h.buffer.preserve (scratchPreservedFrom_put 32 scratch 9 value (by omega))

theorem inputLoad_fetch {extra pc address index offset : Nat} {program : Program}
    (hfetch : program[pc]? = some (.inputLoad address index)) (hoffset : offset < 16) :
    (compile extra program)[location pc + offset]? =
      (inputLoadBody pc address index)[offset]? := by
  rw [compile_get_paddedBody extra program pc (.inputLoad address index) hfetch offset hoffset]
  simp [paddedBody, body, inputLoadBody, TapeRamVirtualCompiler.readCell,
    TapeRamVirtualCompiler.writeCell]

/-- The shared five-instruction prefix samples the virtual index and computes
the nonnegative gap from the original input length. -/
theorem inputLoad_head {v extra cursor address index : Nat} {values : List Nat}
    {program : Program} {source : State} {scratch : Nat → Nat}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hfetch : program[source.pc]? = some (.inputLoad address index))
    (hnormal : Normalized v source.mem) (hscratch : AdapterScratch v values cursor scratch) :
    let offset := source.mem (index % 2 ^ v)
    let after := put (put (put scratch 2 (2 * (index % 2 ^ v))) 5 offset)
      9 (values.length - offset)
    AdapterScratch v values cursor after ∧
      run (v + 1) (compile extra program) 5
        (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 5) source.mem after [] source.out) := by
  dsimp only
  let offset := source.mem (index % 2 ^ v)
  let loaded := put (put scratch 2 (2 * (index % 2 ^ v))) 5 offset
  let after := put loaded 9 (values.length - offset)
  have hlarge : 64 < 2 ^ (v + 1) := by rw [Nat.pow_succ]; omega
  have hloaded : AdapterScratch v values cursor loaded :=
    put_low (put_low hscratch 2 _ (by omega) (by omega)) 5 _ (by omega) (by omega)
  refine ⟨put_temporary hloaded _, ?_⟩
  let code := TapeRamVirtualCompiler.readCell 11 index ++ [.sub 19 13 11]
  have hcode : code.length = 5 := rfl
  have hlinear : ∀ i ∈ code, StraightLine i := by
    simp [code, TapeRamVirtualCompiler.readCell, StraightLine]
  have hprefix : ∀ k, k < code.length →
      (compile extra program)[(state values (location source.pc) source.mem scratch [] source.out).pc + k]? =
        code[k]? := by
    intro k hk
    have hk' : k < 5 := by simpa [hcode] using hk
    change (compile extra program)[location source.pc + k]? = code[k]?
    rw [inputLoad_fetch hfetch (by omega)]
    interval_cases k <;> simp [code, inputLoadBody, TapeRamVirtualCompiler.readCell, TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister, TapeRamVirtualCompiler.twoRegister, temporaryRegister, lengthRegister, baseRegister]
  rw [← hcode, run_eq_execute _ _ _ _ hlinear hprefix]
  dsimp only [code]
  rw [execute_append]
  rw [readCell_execute v (location source.pc) index 5 source.mem scratch [] source.out
    (by omega) (by omega) hscratch.compiler.1 hscratch.compiler.2 hnormal]
  simp only [Option.bind_some]
  have hgap : values.length - offset < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hsub := binaryRegister_execute (original := values) .sub v (location source.pc + 4)
    9 6 5 source.mem loaded [] source.out (by omega) (by omega) (by omega)
  simpa [loaded, after, offset, BinaryKind.instruction, BinaryKind.value,
    hscratch.length_eq, Nat.mod_eq_of_lt hgap, Nat.add_assoc, TapeRamVirtualCompiler.readCell] using hsub

/-- The write suffix begins at code offset eleven on either lookup branch. -/
theorem inputLoad_write {v extra cursor address index : Nat} {values : List Nat}
    {program : Program} {source : State} {scratch : Nat → Nat}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hfetch : program[source.pc]? = some (.inputLoad address index))
    (hscratch : AdapterScratch v values cursor scratch) :
    ∃ nextScratch, AdapterScratch v values cursor nextScratch ∧
      run (v + 1) (compile extra program) 5
        (state values (location source.pc + 11) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16)
          (setCell v source.mem address (scratch 5)) nextScratch [] source.out) := by
  have hlarge : 64 < 2 ^ (v + 1) := by rw [Nat.pow_succ]; omega
  let next := put (put scratch 2 (2 * (address % 2 ^ v))) 5 (scratch 5 % 2 ^ v)
  refine ⟨next, put_low (put_low hscratch 2 _ (by omega) (by omega))
    5 _ (by omega) (by omega), ?_⟩
  have hlinear : ∀ i ∈ TapeRamVirtualCompiler.writeCell address, StraightLine i := by
    simp [TapeRamVirtualCompiler.writeCell, StraightLine]
  have hprefix : ∀ k, k < (TapeRamVirtualCompiler.writeCell address).length →
      (compile extra program)[(state values (location source.pc + 11) source.mem scratch [] source.out).pc + k]? =
        (TapeRamVirtualCompiler.writeCell address)[k]? := by
    intro k hk
    have hk' : k < 5 := hk
    change (compile extra program)[location source.pc + 11 + k]? = _
    rw [Nat.add_assoc, inputLoad_fetch hfetch (by omega)]
    interval_cases k <;> simp [inputLoadBody, TapeRamVirtualCompiler.readCell,
      TapeRamVirtualCompiler.writeCell]
  change run (v + 1) (compile extra program) (TapeRamVirtualCompiler.writeCell address).length _ = _
  rw [run_eq_execute _ _ _ _ hlinear hprefix]
  simpa [next, Nat.add_assoc] using writeCell_execute (original := values)
    v (location source.pc + 11) address source.mem scratch [] source.out
    (by omega) hscratch.compiler.1 hscratch.compiler.2

/-- Follow the in-range branch and load the protected snapshot word. -/
theorem inputLoad_hit {v extra cursor address index offset : Nat} {values : List Nat}
    {program : Program} {source : State} {scratch : Nat → Nat}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hfetch : program[source.pc]? = some (.inputLoad address index))
    (hscratch : AdapterScratch v values cursor scratch)
    (hindex : scratch 5 = offset) (hgap : scratch 9 = values.length - offset)
    (hhit : offset < values.length) :
    ∃ after, AdapterScratch v values cursor after ∧
      after 5 = (values[offset]'hhit) % 2 ^ (v + 1) ∧
      run (v + 1) (compile extra program) 5
        (state values (location source.pc + 5) source.mem scratch [] source.out) =
        some (state values (location source.pc + 11) source.mem after [] source.out) := by
  have hlarge : 64 < 2 ^ (v + 1) := by rw [Nat.pow_succ]; omega
  have hbufferBound := buffer_address_lt hcapacity hhit
  have hdoubleBound : 2 * offset < 2 ^ (v + 1) := by omega
  let after := put (put scratch 2 (65 + 2 * offset)) 5 (values[offset] % 2 ^ (v + 1))
  refine ⟨after, put_low (put_low hscratch 2 _ (by omega) (by omega))
    5 _ (by omega) (by omega), by simp [after], ?_⟩
  have h5 : (compile extra program)[location source.pc + 5]? =
      some (.jzero 19 (location source.pc + 10)) := by
    simpa [inputLoadBody, TapeRamVirtualCompiler.readCell, TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister, TapeRamVirtualCompiler.twoRegister, temporaryRegister, lengthRegister, baseRegister] using
      (inputLoad_fetch hfetch (offset := 5) (by omega))
  have h6 : (compile extra program)[location source.pc + 6]? = some (.mul 5 11 3) := by
    simpa [inputLoadBody, TapeRamVirtualCompiler.readCell, TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister, TapeRamVirtualCompiler.twoRegister, temporaryRegister, lengthRegister, baseRegister] using
      (inputLoad_fetch hfetch (offset := 6) (by omega))
  have h7 : (compile extra program)[location source.pc + 7]? = some (.add 5 5 21) := by
    simpa [inputLoadBody, TapeRamVirtualCompiler.readCell, TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister, TapeRamVirtualCompiler.twoRegister, temporaryRegister, lengthRegister, baseRegister] using
      (inputLoad_fetch hfetch (offset := 7) (by omega))
  have h8 : (compile extra program)[location source.pc + 8]? = some (.load 11 5) := by
    simpa [inputLoadBody, TapeRamVirtualCompiler.readCell, TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister, TapeRamVirtualCompiler.twoRegister, temporaryRegister, lengthRegister, baseRegister] using
      (inputLoad_fetch hfetch (offset := 8) (by omega))
  have h9 : (compile extra program)[location source.pc + 9]? =
      some (.jump (location source.pc + 11)) := by
    simpa [inputLoadBody, TapeRamVirtualCompiler.readCell, TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister, TapeRamVirtualCompiler.twoRegister, temporaryRegister, lengthRegister, baseRegister] using
      (inputLoad_fetch hfetch (offset := 9) (by omega))
  have hmod3 : 3 % 2 ^ (v + 1) = 3 := Nat.mod_eq_of_lt (by omega)
  have hmod5 : 5 % 2 ^ (v + 1) = 5 := Nat.mod_eq_of_lt (by omega)
  have hmod11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
  have hmod19 : 19 % 2 ^ (v + 1) = 19 := Nat.mod_eq_of_lt (by omega)
  have hmod21 : 21 % 2 ^ (v + 1) = 21 := Nat.mod_eq_of_lt (by omega)
  have hset5 (sc : Nat → Nat) (value : Nat) :
      setCell (v + 1) (merge source.mem sc) 5 value =
        merge source.mem (put sc 2 (value % 2 ^ (v + 1))) :=
    set_odd v source.mem sc 5 value (by decide) (by omega)
  have hset11 (sc : Nat → Nat) (value : Nat) :
      setCell (v + 1) (merge source.mem sc) 11 value =
        merge source.mem (put sc 5 (value % 2 ^ (v + 1))) :=
    set_odd v source.mem sc 11 value (by decide) (by omega)
  have hread3 (sc : Nat → Nat) : merge source.mem sc 3 = sc 1 := by simp [merge]
  have hread5 (sc : Nat → Nat) : merge source.mem sc 5 = sc 2 := by simp [merge]
  have hread11 (sc : Nat → Nat) : merge source.mem sc 11 = sc 5 := by simp [merge]
  have hread19 (sc : Nat → Nat) : merge source.mem sc 19 = sc 9 := by simp [merge]
  have hread21 (sc : Nat → Nat) : merge source.mem sc 21 = sc 10 := by simp [merge]
  have hreadBuffer (sc : Nat → Nat) : merge source.mem sc (65 + 2 * offset) =
      sc (32 + offset) := by
    convert merge_odd source.mem sc (32 + offset) using 1 <;> congr 1 <;> omega
  have hbuffer : scratch (32 + offset) = values[offset] := hscratch.buffer offset hhit
  have hpositive : values.length - offset ≠ 0 := by omega
  have haddr : 2 * offset + 65 = 65 + 2 * offset := by omega
  have hhigh2 : 32 + offset ≠ 2 := by omega
  have hhigh5 : 32 + offset ≠ 5 := by omega
  simp [run, step, state, h5, h6, h7, h8, h9, Instr.effect,
    hmod3, hmod5, hmod11, hmod19, hmod21, hread3, hread5, hread11,
    hread19, hread21, hset5, hset11, hgap, hpositive, hindex,
    hscratch.compiler.2, hscratch.base_eq, Nat.mul_comm offset 2,
    Nat.mod_eq_of_lt hdoubleBound, Nat.mod_eq_of_lt hbufferBound,
    hreadBuffer, put, hbuffer, after, Nat.add_assoc, haddr, hhigh2, hhigh5]

/-- The out-of-range path stores zero without accessing the snapshot. -/
theorem inputLoad_miss {v extra cursor address index offset : Nat} {values : List Nat}
    {program : Program} {source : State} {scratch : Nat → Nat}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hfetch : program[source.pc]? = some (.inputLoad address index))
    (hscratch : AdapterScratch v values cursor scratch)
    (hgap : scratch 9 = values.length - offset) (hmiss : values.length ≤ offset) :
    ∃ after, AdapterScratch v values cursor after ∧ after 5 = 0 ∧
      run (v + 1) (compile extra program) 2
        (state values (location source.pc + 5) source.mem scratch [] source.out) =
        some (state values (location source.pc + 11) source.mem after [] source.out) := by
  have hlarge : 64 < 2 ^ (v + 1) := by rw [Nat.pow_succ]; omega
  refine ⟨put scratch 5 0, put_low hscratch 5 0 (by omega) (by omega), by simp, ?_⟩
  have h5 : (compile extra program)[location source.pc + 5]? =
      some (.jzero 19 (location source.pc + 10)) := by
    simpa [inputLoadBody, TapeRamVirtualCompiler.readCell, TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister, TapeRamVirtualCompiler.twoRegister, temporaryRegister, lengthRegister, baseRegister] using
      (inputLoad_fetch hfetch (offset := 5) (by omega))
  have h10 : (compile extra program)[location source.pc + 10]? = some (.set 11 0) := by
    simpa [inputLoadBody, TapeRamVirtualCompiler.readCell, TapeRamVirtualCompiler.resultRegister, TapeRamVirtualCompiler.addressRegister, TapeRamVirtualCompiler.twoRegister, temporaryRegister, lengthRegister, baseRegister] using
      (inputLoad_fetch hfetch (offset := 10) (by omega))
  have hmod19 : 19 % 2 ^ (v + 1) = 19 := Nat.mod_eq_of_lt (by omega)
  have hread19 : merge source.mem scratch 19 = scratch 9 := by simp [merge]
  have hset := set_odd v source.mem scratch 11 0 (by decide) (by omega)
  simp [run, step, state, h5, h10, Instr.effect, hmod19, hread19, hgap,
    Nat.sub_eq_zero_of_le hmiss, hset, Nat.add_assoc]

/-- Indexed input is implemented entirely through the protected snapshot.
Both branch paths finish at the common slot sixteen, before program control
is advanced by the compiler's final branch instructions. -/
theorem inputLoad_run {v extra cursor address index : Nat} {values : List Nat}
    {program : Program} {source : State} {scratch : Nat → Nat}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hfetch : program[source.pc]? = some (.inputLoad address index))
    (hnormal : Normalized v source.mem) (hscratch : AdapterScratch v values cursor scratch) :
    ∃ steps ≤ 16, ∃ nextScratch,
      AdapterScratch v values cursor nextScratch ∧
      run (v + 1) (compile extra program) steps
        (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16)
          (setCell v source.mem address ((values[source.mem (index % 2 ^ v)]?).getD 0))
          nextScratch [] source.out) := by
  let offset := source.mem (index % 2 ^ v)
  let after := put (put (put scratch 2 (2 * (index % 2 ^ v))) 5 offset)
    9 (values.length - offset)
  obtain ⟨hafter, hhead⟩ := inputLoad_head (extra := extra) hcapacity hfetch hnormal hscratch
  change AdapterScratch v values cursor after at hafter
  change run (v + 1) (compile extra program) 5
    (state values (location source.pc) source.mem scratch [] source.out) =
    some (state values (location source.pc + 5) source.mem after [] source.out) at hhead
  have hindex : after 5 = offset := by simp [after]
  have hgap : after 9 = values.length - offset := by simp [after]
  by_cases hhit : offset < values.length
  · obtain ⟨loaded, hloaded, hvalue, hmiddle⟩ :=
      inputLoad_hit (extra := extra) hcapacity hfetch hafter hindex hgap hhit
    obtain ⟨nextScratch, hnext, hwrite⟩ :=
      inputLoad_write (extra := extra) hcapacity hfetch hloaded
    refine ⟨15, by omega, nextScratch, hnext, ?_⟩
    have hmem : setCell v source.mem address (loaded 5) =
        setCell v source.mem address ((values[offset]?).getD 0) := by
      rw [hvalue]
      funext a
      simp [setCell, hhit, mod_physical_virtual]
    rw [show 15 = 5 + (5 + 5) by omega, run_add, hhead, Option.bind_some,
      run_add, hmiddle, Option.bind_some, hwrite]
    simp only [hmem, offset]
  · obtain ⟨loaded, hloaded, hvalue, hmiddle⟩ :=
      inputLoad_miss (extra := extra) hcapacity hfetch hafter hgap (by omega)
    obtain ⟨nextScratch, hnext, hwrite⟩ :=
      inputLoad_write (extra := extra) hcapacity hfetch hloaded
    refine ⟨12, by omega, nextScratch, hnext, ?_⟩
    have hmem : setCell v source.mem address (loaded 5) =
        setCell v source.mem address ((values[offset]?).getD 0) := by
      simp [hvalue, List.getElem?_eq_none (by omega : values.length ≤ offset)]
    rw [show 12 = 5 + (2 + 5) by omega, run_add, hhead, Option.bind_some,
      run_add, hmiddle, Option.bind_some, hwrite]
    simp only [hmem, offset]

end Lax759944Proofs.TapeRamBufferedIndexed
