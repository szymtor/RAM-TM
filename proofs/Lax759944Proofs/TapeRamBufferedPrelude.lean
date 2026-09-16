import Lax759944Proofs.TapeRamBufferedState
import Mathlib.Tactic.IntervalCases

namespace Lax759944Proofs.TapeRamBufferedPrelude

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler

theorem execute_cons (w : Nat) (instruction : Instr) (rest : Program) (s : State) :
    execute w (instruction :: rest) s =
      (execute w [instruction] s).bind (execute w rest) :=
  execute_append w [instruction] rest s

/-- The adapter registers initialized before the snapshot loop. -/
def CoreScratch (v : Nat) (values : List Nat) (scratch : Nat → Nat) : Prop :=
  CompilerScratch v scratch ∧ scratch 6 = values.length ∧ scratch 7 = 0 ∧
    scratch 10 = 65 ∧ scratch 11 = 1 ∧ scratch 12 = 0

def initialCode (extra : Nat) : Program := TapeRamVirtualCompiler.prelude ++
  [.set oneRegister 1, .set baseRegister 65, .set zeroRegister 0,
   .read headerRegister, .set lengthRegister extra,
   .add lengthRegister headerRegister lengthRegister, .set cursorRegister 0,
   .store baseRegister headerRegister, .set temporaryRegister 67,
   .sub remainingRegister lengthRegister oneRegister]

def initialScratch (v header : Nat) (tail : List Nat) : Nat → Nat :=
  put (put (put (put (put (put (put (put (put (put (put
    (fun _ => 0) 1 2) 0 (2 ^ v - 1)) 11 1) 10 65) 12 0) 13 header)
    6 (header :: tail).length) 7 0) 32 header) 9 67) 8 tail.length

theorem initialScratch_core (v header : Nat) (tail : List Nat) :
    CoreScratch v (header :: tail) (initialScratch v header tail) := by
  simp [CoreScratch, CompilerScratch, initialScratch, put]

theorem initialScratch_buffer (v header : Nat) (tail : List Nat) :
    TapeRamBufferedState.BufferStored [header] (initialScratch v header tail) := by
  intro index hindex
  have hi : index = 0 := by simpa using hindex
  subst index
  simp [initialScratch, put, bufferBase]

/-- A store through one odd register writes an odd snapshot cell. -/
theorem storeRegister_execute (v pc addressRegister valueRegister target : Nat)
    (memory scratch : Nat → Nat) (original input output : List Nat)
    (ha : 2 * addressRegister + 1 < 2 ^ (v + 1))
    (hv : 2 * valueRegister + 1 < 2 ^ (v + 1))
    (ht : 2 * target + 1 < 2 ^ (v + 1))
    (haddress : scratch addressRegister = 2 * target + 1) :
    execute (v + 1) [.store (2 * addressRegister + 1) (2 * valueRegister + 1)]
      (state original pc memory scratch input output) =
      some (state original (pc + 1) memory
        (put scratch target (scratch valueRegister % 2 ^ (v + 1))) input output) := by
  have hs := set_odd v memory scratch (2 * target + 1) (scratch valueRegister) (by omega) ht
  simp only [execute, Instr.effect, state, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hv,
    merge_odd, haddress, hs, Option.bind_some]
  simpa [Nat.add_div, Nat.mul_div_right]

theorem addRegister_execute (v pc target left right : Nat) {original : List Nat}
    (memory scratch : Nat → Nat) (input output : List Nat)
    (htarget : 2 * target + 1 < 2 ^ (v + 1))
    (hleft : 2 * left + 1 < 2 ^ (v + 1))
    (hright : 2 * right + 1 < 2 ^ (v + 1)) :
    execute (v + 1) [.add (2 * target + 1) (2 * left + 1) (2 * right + 1)]
      (state original pc memory scratch input output) =
      some (state original (pc + 1) memory
        (put scratch target ((scratch left + scratch right) % 2 ^ (v + 1)))
        input output) := by
  simpa only [BinaryKind.instruction, BinaryKind.value] using
    (binaryRegister_execute .add v pc target left right memory scratch input output
      htarget hleft hright (original := original))

theorem subRegister_execute (v pc target left right : Nat) {original : List Nat}
    (memory scratch : Nat → Nat) (input output : List Nat)
    (htarget : 2 * target + 1 < 2 ^ (v + 1))
    (hleft : 2 * left + 1 < 2 ^ (v + 1))
    (hright : 2 * right + 1 < 2 ^ (v + 1)) :
    execute (v + 1) [.sub (2 * target + 1) (2 * left + 1) (2 * right + 1)]
      (state original pc memory scratch input output) =
      some (state original (pc + 1) memory
        (put scratch target ((scratch left - scratch right) % 2 ^ (v + 1)))
        input output) := by
  simpa only [BinaryKind.instruction, BinaryKind.value] using
    (binaryRegister_execute .sub v pc target left right memory scratch input output
      htarget hleft hright (original := original))

theorem initialCode_execute (v extra header : Nat) (tail : List Nat)
    (hcapacity : (header :: tail).length + 32 < 2 ^ v)
    (hlength : (header :: tail).length = header + extra)
    (hwords : ∀ value ∈ header :: tail, value < 2 ^ v) :
    execute (v + 1) (initialCode extra) (initState (header :: tail)) =
      some (state (header :: tail) 14 (fun _ => 0)
        (initialScratch v header tail) tail []) := by
  have hpow : 2 ^ (v + 1) = 2 ^ v * 2 := Nat.pow_succ _ _
  have hnonempty : 0 < (header :: tail).length := by simp
  have hh : header < 2 ^ v := hwords header (by simp)
  have hsmall : 16 ≤ 2 ^ (v + 1) := by omega
  have hinitial : initState (header :: tail) =
      state (header :: tail) 0 (fun _ => 0) (fun _ => 0) (header :: tail) [] := by
    simp only [initState, state]
    congr 1
    funext address
    simp [merge]
  rw [hinitial, initialCode, execute_append,
    prelude_execute v 0 (fun _ => 0) (fun _ => 0) (header :: tail) [] hsmall]
  simp only [Option.bind_some]
  simp only [oneRegister, baseRegister, zeroRegister, headerRegister, lengthRegister,
    cursorRegister, temporaryRegister, remainingRegister, Nat.zero_add]
  rw [execute_cons, setRegister_execute v 4 11 1 _ _ _ _ (by omega), Option.bind_some]
  rw [execute_cons, setRegister_execute v 5 10 65 _ _ _ _ (by omega), Option.bind_some]
  rw [execute_cons, setRegister_execute v 6 12 0 _ _ _ _ (by omega), Option.bind_some]
  rw [execute_cons, readRegister_execute v 7 13 header tail _ _ _ (by omega), Option.bind_some]
  rw [execute_cons, setRegister_execute v 8 6 extra _ _ _ _ (by omega), Option.bind_some]
  rw [execute_cons, addRegister_execute v 9 6 13 6 _ _ _ _
    (by omega) (by omega) (by omega), Option.bind_some]
  rw [execute_cons, setRegister_execute v 10 7 0 _ _ _ _ (by omega), Option.bind_some]
  rw [execute_cons, storeRegister_execute v 11 10 13 32 _ _ _ _ _
    (by omega) (by omega) (by omega) (by
      simp (disch := omega) [put, Nat.mod_eq_of_lt]), Option.bind_some]
  rw [execute_cons, setRegister_execute v 12 9 67 _ _ _ _ (by omega), Option.bind_some]
  rw [execute_cons, subRegister_execute v 13 8 6 11 _ _ _ _
    (by omega) (by omega) (by omega), Option.bind_some]
  simp (disch := omega) only [execute, BinaryKind.value, put_same, put_other,
    Nat.mod_eq_of_lt, Nat.zero_mod, put_overwrite]
  simpa only [initialScratch, ← hlength, List.length_cons, Nat.add_sub_cancel]



theorem compile_get_prelude (extra : Nat) (program : Program) (index : Nat)
    (hindex : index < 20) :
    (compile extra program)[index]? = (prelude extra)[index]? := by
  have hprefix : index < (prelude extra ++ blocks program.length 0 program).length := by
    simp only [List.length_append, prelude_length, blocks_length]
    omega
  simp only [compile, List.getElem?_append, hprefix, prelude_length, hindex, ↓reduceIte]

theorem initialCode_run (v extra header : Nat) (tail : List Nat) (program : Program)
    (hcapacity : (header :: tail).length + 32 < 2 ^ v)
    (hlength : (header :: tail).length = header + extra)
    (hwords : ∀ value ∈ header :: tail, value < 2 ^ v) :
    run (v + 1) (compile extra program) 14 (initState (header :: tail)) =
      some (state (header :: tail) 14 (fun _ => 0)
        (initialScratch v header tail) tail []) := by
  have hlinear : ∀ instruction ∈ initialCode extra, StraightLine instruction := by
    simp [initialCode, TapeRamVirtualCompiler.prelude, StraightLine]
  have hfetch : ∀ index, index < (initialCode extra).length →
      (compile extra program)[(initState (header :: tail)).pc + index]? =
        (initialCode extra)[index]? := by
    intro index hindex
    have hi : index < 14 := by simpa [initialCode, TapeRamVirtualCompiler.prelude] using hindex
    interval_cases index <;> rfl
  change run (v + 1) (compile extra program) (initialCode extra).length _ = _
  rw [run_eq_execute _ _ _ _ hlinear hfetch]
  exact initialCode_execute v extra header tail hcapacity hlength hwords

theorem CoreScratch.put {v : Nat} {values : List Nat} {scratch : Nat → Nat}
    (hcore : CoreScratch v values scratch) (index value : Nat)
    (hindex : index = 5 ∨ index = 8 ∨ index = 9 ∨ 32 ≤ index) :
    CoreScratch v values (put scratch index value) := by
  rcases hcore with ⟨⟨hmask, htwo⟩, hlength, hcursor, hbase, hone, hzero⟩
  rcases hindex with rfl | rfl | rfl | hindex <;>
    simp (disch := omega) [CoreScratch, CompilerScratch, put,
      hmask, htwo, hlength, hcursor, hbase, hone, hzero]

theorem buffer_put_low {consumed : List Nat} {scratch : Nat → Nat}
    (hbuffer : TapeRamBufferedState.BufferStored consumed scratch)
    (index value : Nat) (hindex : index < 32) :
    TapeRamBufferedState.BufferStored consumed (put scratch index value) :=
  hbuffer.preserve (scratchPreservedFrom_put 32 scratch index value hindex)

theorem buffer_snoc {consumed : List Nat} {scratch : Nat → Nat}
    (hbuffer : TapeRamBufferedState.BufferStored consumed scratch) (value : Nat) :
    TapeRamBufferedState.BufferStored (consumed ++ [value])
      (put scratch (32 + consumed.length) value) := by
  intro index hindex
  by_cases hprefix : index < consumed.length
  · rw [List.getElem_append_left hprefix]
    simpa [put, bufferBase, show index ≠ consumed.length by omega] using
      hbuffer index hprefix
  · have hi : index = consumed.length := by simp only [List.length_append, List.length_singleton] at hindex; omega
    subst index
    simp [put, bufferBase]

def loopCode : Program :=
  [.read TapeRamVirtualCompiler.resultRegister,
   .store temporaryRegister TapeRamVirtualCompiler.resultRegister,
   .add temporaryRegister temporaryRegister TapeRamVirtualCompiler.twoRegister,
   .sub remainingRegister remainingRegister oneRegister]

def loopScratch (scratch : Nat → Nat) (consumed : List Nat) (value : Nat)
    (rest : List Nat) : Nat → Nat :=
  put (put (put (put scratch 5 value) (32 + consumed.length) value)
    9 (65 + 2 * (consumed.length + 1))) 8 rest.length

theorem loopCode_execute (v : Nat) (original consumed : List Nat) (value : Nat)
    (rest : List Nat) (scratch : Nat → Nat)
    (hcapacity : original.length + 32 < 2 ^ v)
    (hsplit : original = consumed ++ value :: rest)
    (hvalue : value < 2 ^ v)
    (hcore : CoreScratch v original scratch)
    (hremaining : scratch 8 = (value :: rest).length)
    (hpointer : scratch 9 = 65 + 2 * consumed.length) :
    execute (v + 1) loopCode
      (state original 15 (fun _ => 0) scratch (value :: rest) []) =
      some (state original 19 (fun _ => 0)
        (loopScratch scratch consumed value rest) rest []) := by
  have hpow : 2 ^ (v + 1) = 2 ^ v * 2 := Nat.pow_succ _ _
  have hlength : original.length = consumed.length + (rest.length + 1) := by simp [hsplit]
  rcases hcore with ⟨⟨hmask, htwo⟩, hlen, hcursor, hbase, hone, hzero⟩
  simp only [loopCode, TapeRamVirtualCompiler.resultRegister,
    TapeRamVirtualCompiler.twoRegister, temporaryRegister, remainingRegister, oneRegister]
  rw [execute_cons,
    readRegister_execute v 15 5 value rest _ _ _ (by omega), Option.bind_some]
  rw [execute_cons, storeRegister_execute v 16 9 5 (32 + consumed.length) _ _ _ _ _
    (by omega) (by omega) (by omega) (by simp [put, hpointer]; omega), Option.bind_some]
  rw [execute_cons, addRegister_execute v 17 9 9 1 _ _ _ _
    (by omega) (by omega) (by omega), Option.bind_some]
  rw [execute_cons, subRegister_execute v 18 8 8 11 _ _ _ _
    (by omega) (by omega) (by omega), Option.bind_some]
  simp (disch := omega) only [execute, BinaryKind.value, put_same, put_other,
    Nat.mod_eq_of_lt, hremaining, hpointer, htwo, hone, List.length_cons,
    Nat.add_sub_cancel]
  simp only [loopScratch, Nat.mul_add, Nat.mul_one, Nat.add_assoc]


theorem loop_iteration (v extra : Nat) (program : Program)
    (original consumed : List Nat) (value : Nat) (rest : List Nat) (scratch : Nat → Nat)
    (hcapacity : original.length + 32 < 2 ^ v)
    (hsplit : original = consumed ++ value :: rest)
    (hvalue : value < 2 ^ v)
    (hcore : CoreScratch v original scratch)
    (hremaining : scratch 8 = (value :: rest).length)
    (hpointer : scratch 9 = 65 + 2 * consumed.length) :
    run (v + 1) (compile extra program) 6
      (state original 14 (fun _ => 0) scratch (value :: rest) []) =
      some (state original 14 (fun _ => 0)
        (loopScratch scratch consumed value rest) rest []) := by
  have hpow : 2 ^ (v + 1) = 2 ^ v * 2 := Nat.pow_succ _ _
  have h17 : 17 < 2 ^ (v + 1) := by omega
  have h14 : (compile extra program)[14]? =
      some (.jzero remainingRegister (location 0)) := rfl
  have h19 : (compile extra program)[19]? = some (.jump 14) := rfl
  have hfirst : run (v + 1) (compile extra program) 1
      (state original 14 (fun _ => 0) scratch (value :: rest) []) =
      some (state original 15 (fun _ => 0) scratch (value :: rest) []) := by
    simp [run, step, state, h14, Instr.effect, remainingRegister,
      Nat.mod_eq_of_lt h17, merge, hremaining]
  have hbody : run (v + 1) (compile extra program) 4
      (state original 15 (fun _ => 0) scratch (value :: rest) []) =
      some (state original 19 (fun _ => 0)
        (loopScratch scratch consumed value rest) rest []) := by
    have hlinear : ∀ instruction ∈ loopCode, StraightLine instruction := by
      simp [loopCode, StraightLine]
    have hfetch : ∀ index, index < loopCode.length →
        (compile extra program)[(state original 15 (fun _ => 0) scratch
          (value :: rest) []).pc + index]? = loopCode[index]? := by
      intro index hindex
      have hi : index < 4 := by simpa [loopCode] using hindex
      interval_cases index <;> rfl
    change run (v + 1) (compile extra program) loopCode.length _ = _
    rw [run_eq_execute _ _ _ _ hlinear hfetch]
    exact loopCode_execute v original consumed value rest scratch
      hcapacity hsplit hvalue hcore hremaining hpointer
  have hlast : run (v + 1) (compile extra program) 1
      (state original 19 (fun _ => 0) (loopScratch scratch consumed value rest) rest []) =
      some (state original 14 (fun _ => 0) (loopScratch scratch consumed value rest) rest []) := by
    simp [run, step, state, h19, Instr.effect]
  rw [show 6 = 1 + (4 + 1) by rfl, run_add, hfirst, Option.bind_some,
    run_add, hbody, Option.bind_some, hlast]

theorem loop_runs (v extra : Nat) (program : Program) (original : List Nat)
    (consumed rest : List Nat) (scratch : Nat → Nat)
    (hcapacity : original.length + 32 < 2 ^ v)
    (hsplit : original = consumed ++ rest)
    (hwords : ∀ value ∈ original, value < 2 ^ v)
    (hcore : CoreScratch v original scratch)
    (hremaining : scratch 8 = rest.length)
    (hpointer : scratch 9 = 65 + 2 * consumed.length)
    (hbuffer : TapeRamBufferedState.BufferStored consumed scratch) :
    ∃ finalScratch,
      TapeRamBufferedState.AdapterScratch v original 0 finalScratch ∧
      run (v + 1) (compile extra program) (6 * rest.length + 1)
        (state original 14 (fun _ => 0) scratch rest []) =
        some (state original (location 0) (fun _ => 0) finalScratch [] []) := by
  induction rest generalizing consumed scratch with
  | nil =>
      rcases hcore with ⟨hcompiler, hlength, hcursor, hbase, hone, hzero⟩
      refine ⟨scratch, ⟨hcompiler, hlength, hcursor, hbase, hone, hzero,
        Nat.zero_le _, ?_⟩, ?_⟩
      · simpa [hsplit] using hbuffer
      · have hpow : 2 ^ (v + 1) = 2 ^ v * 2 := Nat.pow_succ _ _
        have h17 : 17 < 2 ^ (v + 1) := by omega
        have h14 : (compile extra program)[14]? =
            some (.jzero remainingRegister (location 0)) := rfl
        simp [run, step, state, h14, Instr.effect, remainingRegister,
          Nat.mod_eq_of_lt h17, merge, hremaining]
  | cons value rest ih =>
      have hvalue : value < 2 ^ v := hwords value (by simp [hsplit])
      let nextScratch := loopScratch scratch consumed value rest
      have hcoreNext : CoreScratch v original nextScratch :=
        (((hcore.put 5 value (by omega)).put (32 + consumed.length) value (by omega)).put
          9 (65 + 2 * (consumed.length + 1)) (by omega)).put 8 rest.length (by omega)
      have hremainingNext : nextScratch 8 = rest.length := by simp [nextScratch, loopScratch]
      have hpointerNext : nextScratch 9 = 65 + 2 * (consumed ++ [value]).length := by
        simp [nextScratch, loopScratch]
      have hbufferNext : TapeRamBufferedState.BufferStored (consumed ++ [value]) nextScratch :=
        buffer_put_low
          (buffer_put_low (buffer_snoc (buffer_put_low hbuffer 5 value (by omega)) value)
            9 (65 + 2 * (consumed.length + 1)) (by omega)) 8 rest.length (by omega)
      have hsplitNext : original = (consumed ++ [value]) ++ rest := by
        simpa only [List.append_assoc, List.singleton_append] using hsplit
      obtain ⟨finalScratch, hfinal, hrun⟩ := ih (consumed ++ [value]) nextScratch
        hsplitNext hcoreNext hremainingNext hpointerNext hbufferNext
      refine ⟨finalScratch, hfinal, ?_⟩
      rw [show 6 * (value :: rest).length + 1 = 6 + (6 * rest.length + 1) by
        simp only [List.length_cons]; omega, run_add,
        loop_iteration v extra program original consumed value rest scratch
          hcapacity hsplit hvalue hcore hremaining hpointer, Option.bind_some]
      exact hrun

/-- Snapshot the complete framed input, preserving zero virtual memory and
charging every initialization, copy, loop-control and final-test transition. -/
theorem compile_start (v extra header : Nat) (tail : List Nat) (program : Program)
    (hcapacity : (header :: tail).length + 32 < 2 ^ v)
    (hlength : (header :: tail).length = header + extra)
    (hwords : ∀ value ∈ header :: tail, value < 2 ^ v) :
    ∃ scratch,
      TapeRamBufferedState.AdapterScratch v (header :: tail) 0 scratch ∧
      run (v + 1) (compile extra program) (6 * (header :: tail).length + 9)
        (initState (header :: tail)) =
        some (state (header :: tail) (location 0) (fun _ => 0) scratch [] []) := by
  obtain ⟨scratch, hscratch, hloop⟩ := loop_runs v extra program (header :: tail)
    [header] tail (initialScratch v header tail) hcapacity rfl hwords
    (initialScratch_core v header tail) (by simp [initialScratch])
    (by simp [initialScratch]) (initialScratch_buffer v header tail)
  refine ⟨scratch, hscratch, ?_⟩
  rw [show 6 * (header :: tail).length + 9 = 14 + (6 * tail.length + 1) by
    simp only [List.length_cons]; omega, run_add,
    initialCode_run v extra header tail program hcapacity hlength hwords, Option.bind_some]
  exact hloop

end Lax759944Proofs.TapeRamBufferedPrelude
