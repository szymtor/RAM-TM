import Lax759944Proofs.TapeRamVirtualMacros

namespace Lax759944Proofs.TapeRamVirtualSimulation

open Lax808846.Ram
open TapeRamVirtualMemory TapeRamVirtualCompiler TapeRamVirtualMacros

def Simulates (v : Nat) (source physical : State) : Prop :=
  ∃ scratch,
    CompilerScratch v scratch ∧ Normalized v source.mem ∧
      physical = state source.input (location source.pc) source.mem scratch source.inp source.out

theorem normalized_init (v : Nat) (input : List Nat) :
    Normalized v (initState input).mem := by
  intro address
  exact Nat.two_pow_pos v

theorem normalized_effect {v : Nat} {i : Instr} {source next : State}
    (hnormal : Normalized v source.mem) (heffect : i.effect v source = some next) :
    Normalized v next.mem := by
  cases i <;> simp only [Instr.effect] at heffect
  all_goals try { cases heffect; exact hnormal }
  case halt => cases heffect
  case read address =>
    cases hi : source.inp.head? with
    | none => rw [hi] at heffect; cases heffect
    | some value =>
      rw [hi] at heffect
      cases heffect
      exact normalized_setCell v source.mem hnormal address value
  all_goals
    cases heffect
    exact normalized_setCell v source.mem hnormal _ _

variable {original : List Nat}

theorem body_set (v pc address value : Nat) (memory scratch : Nat → Nat)
    (input output : List Nat) (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hscratch : CompilerScratch v scratch) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (body (.set address value))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.set address value)).length)
          (setCell v memory address value) nextScratch input output) := by
  rcases hscratch with ⟨hmask, htwo⟩
  rw [show body (.set address value) = [.set 11 value] ++ writeCell address by rfl,
    execute_append, setRegister_execute v pc 5 value memory scratch input output (by omega)]
  simp only [Option.bind_some]
  rw [writeCell_execute v (pc + 1) address memory
    (put scratch 5 (value % 2 ^ (v + 1))) input output hcapacity]
  · let nextScratch :=
      put (put (put scratch 5 (value % 2 ^ (v + 1))) 2
        (2 * (address % 2 ^ v))) 5 (value % 2 ^ v)
    refine ⟨nextScratch, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v _
          (compilerScratch_put v scratch ⟨hmask, htwo⟩ 5 _ (by omega))
          2 _ (by omega)) 5 _ (by omega)
    · intro index hindex
      have h2 : index ≠ 2 := by omega
      have h5 : index ≠ 5 := by omega
      simp [nextScratch, put, h2, h5]
    simp only [body, List.length_append, List.length_cons, List.length_nil,
      Nat.add_zero, writeCell]
    dsimp [nextScratch]
    have hmemory : setCell v memory address (value % 2 ^ (v + 1)) =
        setCell v memory address value := by
      funext a
      simp [setCell, TapeRamVirtualMemory.mod_physical_virtual]
    simp only [put_same]
    rw [hmemory]
    congr 2
    simp [put, TapeRamVirtualMemory.mod_physical_virtual]
  · simp [put, hmask]
  · simp [put, htwo]

def sourceInstruction (kind : BinaryKind) (target left right : Nat) : Instr :=
  match kind with
  | .add => .add target left right
  | .sub => .sub target left right
  | .mul => .mul target left right
  | .div => .div target left right
  | .and => .and target left right
  | .shiftl => .shiftl target left right

theorem body_sourceInstruction (kind : BinaryKind) (target left right : Nat) :
    body (sourceInstruction kind target left right) =
      readCell 7 left ++ readCell 9 right ++
        [kind.instruction 11 7 9] ++ writeCell target := by
  cases kind <;> rfl

theorem body_binary (kind : BinaryKind) (v pc target left right : Nat)
    (memory scratch : Nat → Nat) (input output : List Nat)
    (hcapacity : 16 ≤ 2 ^ (v + 1)) (hscratch : CompilerScratch v scratch)
    (hnormal : Normalized v memory) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (body (sourceInstruction kind target left right))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (sourceInstruction kind target left right)).length)
          (setCell v memory target (kind.value (memory (left % 2 ^ v))
            (memory (right % 2 ^ v)))) nextScratch input output) := by
  rcases hscratch with ⟨hmask, htwo⟩
  let sLeft := put (put scratch 2 (2 * (left % 2 ^ v))) 3 (memory (left % 2 ^ v))
  let sRight := put (put sLeft 2 (2 * (right % 2 ^ v))) 4 (memory (right % 2 ^ v))
  let raw := kind.value (memory (left % 2 ^ v)) (memory (right % 2 ^ v))
  let sResult := put sRight 5 (raw % 2 ^ (v + 1))
  let nextScratch := put (put sResult 2 (2 * (target % 2 ^ v))) 5 (raw % 2 ^ v)
  have hsLeft : CompilerScratch v sLeft :=
    compilerScratch_put v _ (compilerScratch_put v scratch ⟨hmask, htwo⟩ 2 _ (by omega)) 3 _ (by omega)
  have hsRight : CompilerScratch v sRight :=
    compilerScratch_put v _ (compilerScratch_put v sLeft hsLeft 2 _ (by omega)) 4 _ (by omega)
  have hsResult : CompilerScratch v sResult := compilerScratch_put v sRight hsRight 5 _ (by omega)
  have hsNext : CompilerScratch v nextScratch :=
    compilerScratch_put v _ (compilerScratch_put v sResult hsResult 2 _ (by omega)) 5 _ (by omega)
  refine ⟨nextScratch, hsNext, ?_, ?_⟩
  · intro index hindex
    have h2 : index ≠ 2 := by omega
    have h3 : index ≠ 3 := by omega
    have h4 : index ≠ 4 := by omega
    have h5 : index ≠ 5 := by omega
    simp [nextScratch, sResult, sRight, sLeft, put, h2, h3, h4, h5]
  rw [body_sourceInstruction, execute_append, execute_append, execute_append]
  rw [readCell_execute v pc left 3 memory scratch input output hcapacity (by omega)
    hmask htwo hnormal]
  simp only [Option.bind_some]
  rw [readCell_execute v (pc + 4) right 4 memory sLeft input output
    hcapacity (by omega) hsLeft.1 hsLeft.2 hnormal]
  simp only [Option.bind_some]
  rw [binaryRegister_execute kind v (pc + 4 + 4) 5 3 4 memory sRight
    input output (by omega) (by omega) (by omega)]
  simp only [Option.bind_some]
  have hsRightLeft : sRight 3 = memory (left % 2 ^ v) := by
    simp [sRight, sLeft, put]
  have hsRightRight : sRight 4 = memory (right % 2 ^ v) := by
    simp [sRight, sLeft, put]
  rw [hsRightLeft, hsRightRight]
  rw [writeCell_execute v (pc + 4 + 4 + 1) target memory sResult input output hcapacity
    hsResult.1 hsResult.2]
  have hmemory : setCell v memory target (raw % 2 ^ (v + 1)) =
      setCell v memory target raw := by
    funext a
    simp [setCell, TapeRamVirtualMemory.mod_physical_virtual]
  simp only [sResult, put_same]
  rw [hmemory]
  dsimp [sLeft, sRight, raw, sResult, nextScratch]
  congr 2 <;> simp [put, TapeRamVirtualMemory.mod_physical_virtual,
    body_sourceInstruction, readCell, writeCell]

theorem body_read (v pc address value : Nat) (rest : List Nat)
    (memory scratch : Nat → Nat) (output : List Nat)
    (hcapacity : 16 ≤ 2 ^ (v + 1)) (hscratch : CompilerScratch v scratch) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (body (.read address))
        (state original pc memory scratch (value :: rest) output) =
        some (state original (pc + (body (.read address)).length)
          (setCell v memory address value) nextScratch rest output) := by
  rcases hscratch with ⟨hmask, htwo⟩
  let afterRead := put scratch 5 (value % 2 ^ (v + 1))
  let nextScratch := put (put afterRead 2 (2 * (address % 2 ^ v))) 5 (value % 2 ^ v)
  have hsAfter : CompilerScratch v afterRead :=
    compilerScratch_put v scratch ⟨hmask, htwo⟩ 5 _ (by omega)
  have hsNext : CompilerScratch v nextScratch := compilerScratch_put v _
    (compilerScratch_put v afterRead hsAfter 2 _ (by omega)) 5 _ (by omega)
  refine ⟨nextScratch, hsNext, ?_, ?_⟩
  · intro index hindex
    have h2 : index ≠ 2 := by omega
    have h5 : index ≠ 5 := by omega
    simp [nextScratch, afterRead, put, h2, h5]
  rw [show body (.read address) = [.read 11] ++ writeCell address by rfl,
    execute_append]
  have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
  have hset11 := set_odd v memory scratch 11 value (by decide) (by omega)
  simp only [execute, Instr.effect, state, List.head?_cons, List.tail_cons,
    Option.map_some, Option.bind_some, h11, hset11]
  change execute (v + 1) (writeCell address)
    (state original (pc + 1) memory afterRead rest output) = _
  rw [writeCell_execute v (pc + 1) address memory afterRead rest output hcapacity
    hsAfter.1 hsAfter.2]
  simp only [afterRead, put_same]
  have hmemory : setCell v memory address (value % 2 ^ (v + 1)) =
      setCell v memory address value := by
    funext a
    simp [setCell, TapeRamVirtualMemory.mod_physical_virtual]
  rw [hmemory]
  dsimp [afterRead, nextScratch]
  congr 2 <;> simp [TapeRamVirtualMemory.mod_physical_virtual, writeCell]

theorem body_write (v pc address : Nat) (memory scratch : Nat → Nat)
    (input output : List Nat) (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hscratch : CompilerScratch v scratch) (hnormal : Normalized v memory) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (body (.write address))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.write address)).length) memory nextScratch input
          (output ++ [memory (address % 2 ^ v)])) := by
  rcases hscratch with ⟨hmask, htwo⟩
  let nextScratch := put (put scratch 2 (2 * (address % 2 ^ v))) 5
    (memory (address % 2 ^ v))
  have hsNext : CompilerScratch v nextScratch := compilerScratch_put v _
    (compilerScratch_put v scratch ⟨hmask, htwo⟩ 2 _ (by omega)) 5 _ (by omega)
  refine ⟨nextScratch, hsNext, ?_, ?_⟩
  · intro index hindex
    have h2 : index ≠ 2 := by omega
    have h5 : index ≠ 5 := by omega
    simp [nextScratch, put, h2, h5]
  rw [show body (.write address) = readCell 11 address ++ [.write 11] by rfl,
    execute_append, readCell_execute v pc address 5 memory scratch input output
      hcapacity (by omega) hmask htwo hnormal]
  simp only [Option.bind_some, execute, Instr.effect, state]
  have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
  have hvalue : memory (address % 2 ^ v) < 2 ^ (v + 1) :=
    Nat.lt_of_lt_of_le (hnormal _) (Nat.pow_le_pow_right (by decide) (by omega))
  simp [h11, nextScratch, merge, put, Nat.mod_eq_of_lt hvalue, readCell]

theorem body_jzero (v pc address target : Nat) (memory scratch : Nat → Nat)
    (input output : List Nat) (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hscratch : CompilerScratch v scratch) (hnormal : Normalized v memory) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (body (.jzero address target))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.jzero address target)).length) memory nextScratch
          input output) ∧ nextScratch 5 = memory (address % 2 ^ v) := by
  rcases hscratch with ⟨hmask, htwo⟩
  let nextScratch := put (put scratch 2 (2 * (address % 2 ^ v))) 5
    (memory (address % 2 ^ v))
  refine ⟨nextScratch,
    compilerScratch_put v _ (compilerScratch_put v scratch ⟨hmask, htwo⟩ 2 _ (by omega))
      5 _ (by omega), ?_, ?_, by simp [nextScratch]⟩
  · intro index hindex
    have h2 : index ≠ 2 := by omega
    have h5 : index ≠ 5 := by omega
    simp [nextScratch, put, h2, h5]
  simpa [body, readCell] using
    readCell_execute v pc address 5 memory scratch input output hcapacity (by omega)
      hmask htwo hnormal

theorem body_not (v pc target source : Nat) (memory scratch : Nat → Nat)
    (input output : List Nat) (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hscratch : CompilerScratch v scratch) (hnormal : Normalized v memory) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (body (.not target source))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.not target source)).length)
          (setCell v memory target (2 ^ v - 1 - memory (source % 2 ^ v)))
          nextScratch input output) := by
  rcases hscratch with ⟨hmask, htwo⟩
  let afterRead := put (put scratch 2 (2 * (source % 2 ^ v))) 3
    (memory (source % 2 ^ v))
  let complement := 2 ^ v - 1 - memory (source % 2 ^ v)
  let afterSub := put afterRead 5 complement
  let nextScratch := put (put afterSub 2 (2 * (target % 2 ^ v))) 5 complement
  have hsRead : CompilerScratch v afterRead := compilerScratch_put v _
    (compilerScratch_put v scratch ⟨hmask, htwo⟩ 2 _ (by omega)) 3 _ (by omega)
  have hsSub : CompilerScratch v afterSub := compilerScratch_put v afterRead hsRead 5 _ (by omega)
  have hsNext : CompilerScratch v nextScratch := compilerScratch_put v _
    (compilerScratch_put v afterSub hsSub 2 _ (by omega)) 5 _ (by omega)
  refine ⟨nextScratch, hsNext, ?_, ?_⟩
  · intro index hindex
    have h2 : index ≠ 2 := by omega
    have h3 : index ≠ 3 := by omega
    have h5 : index ≠ 5 := by omega
    simp [nextScratch, afterSub, afterRead, put, h2, h3, h5]
  rw [show body (.not target source) =
      readCell 7 source ++ [.sub 11 1 7] ++ writeCell target by rfl,
    execute_append, execute_append,
    readCell_execute v pc source 3 memory scratch input output hcapacity (by omega)
      hmask htwo hnormal]
  simp only [Option.bind_some]
  change (execute (v + 1) [.sub 11 1 7]
    (state original (pc + 4) memory afterRead input output)).bind
      (execute (v + 1) (writeCell target)) = _
  have hvalue : complement < 2 ^ (v + 1) := by
    have := Nat.two_pow_pos v
    rw [Nat.pow_succ]
    omega
  have hsubexec : execute (v + 1) [.sub 11 1 7]
      (state original (pc + 4) memory afterRead input output) =
      some (state original (pc + 4 + 1) memory
        (put afterRead 5 ((afterRead 0 - afterRead 3) % 2 ^ (v + 1))) input output) := by
    simpa [BinaryKind.instruction, BinaryKind.value] using
      binaryRegister_execute .sub v (pc + 4) 5 0 3 memory afterRead input output
        (by omega) (by omega) (by omega)
  rw [hsubexec]
  simp only [Option.bind_some]
  have hzero : afterRead 0 = 2 ^ v - 1 := hsRead.1
  have hthree : afterRead 3 = memory (source % 2 ^ v) := by simp [afterRead]
  rw [hzero, hthree, Nat.mod_eq_of_lt hvalue]
  change execute (v + 1) (writeCell target)
    (state original (pc + 4 + 1) memory afterSub input output) = _
  rw [writeCell_execute v (pc + 4 + 1) target memory afterSub input output hcapacity
    hsSub.1 hsSub.2]
  simp only [afterSub, put_same]
  have hvirtual : complement < 2 ^ v := by
    have := Nat.two_pow_pos v
    omega
  dsimp [afterRead, complement, afterSub, nextScratch]
  congr 2
  rw [Nat.mod_eq_of_lt hvirtual]

theorem body_load (v pc target addressCell : Nat) (memory scratch : Nat → Nat)
    (input output : List Nat) (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hscratch : CompilerScratch v scratch) (hnormal : Normalized v memory) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (body (.load target addressCell))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.load target addressCell)).length)
          (setCell v memory target (memory (memory (addressCell % 2 ^ v))))
          nextScratch input output) := by
  rcases hscratch with ⟨hmask, htwo⟩
  let pointer := memory (addressCell % 2 ^ v)
  let afterRead := put (put scratch 2 (2 * (addressCell % 2 ^ v))) 3 pointer
  let afterDouble := put afterRead 2 (2 * pointer)
  let afterLoad := put afterDouble 5 (memory pointer)
  let nextScratch := put (put afterLoad 2 (2 * (target % 2 ^ v))) 5
    (memory pointer)
  have hpointer : pointer < 2 ^ v := hnormal _
  have hdouble : 2 * pointer < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hloaded : memory pointer < 2 ^ (v + 1) :=
    Nat.lt_of_lt_of_le (hnormal pointer)
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hsRead : CompilerScratch v afterRead := compilerScratch_put v _
    (compilerScratch_put v scratch ⟨hmask, htwo⟩ 2 _ (by omega)) 3 _ (by omega)
  have hsDouble : CompilerScratch v afterDouble :=
    compilerScratch_put v afterRead hsRead 2 _ (by omega)
  have hsLoad : CompilerScratch v afterLoad :=
    compilerScratch_put v afterDouble hsDouble 5 _ (by omega)
  have hsNext : CompilerScratch v nextScratch := compilerScratch_put v _
    (compilerScratch_put v afterLoad hsLoad 2 _ (by omega)) 5 _ (by omega)
  refine ⟨nextScratch, hsNext, ?_, ?_⟩
  · intro index hindex
    have h2 : index ≠ 2 := by omega
    have h3 : index ≠ 3 := by omega
    have h5 : index ≠ 5 := by omega
    simp [nextScratch, afterLoad, afterDouble, afterRead, put, h2, h3, h5]
  rw [show body (.load target addressCell) =
      readCell 7 addressCell ++ [.mul 5 7 3] ++ [.load 11 5] ++
        writeCell target by rfl,
    execute_append, execute_append, execute_append,
    readCell_execute v pc addressCell 3 memory scratch input output hcapacity
      (by omega) hmask htwo hnormal]
  simp only [Option.bind_some]
  have hmul : execute (v + 1) [.mul 5 7 3]
      (state original (pc + 4) memory afterRead input output) =
      some (state original (pc + 4 + 1) memory afterDouble input output) := by
    rw [show [.mul 5 7 3] =
        [BinaryKind.instruction .mul (2 * 2 + 1) (2 * 3 + 1) (2 * 1 + 1)] by
          rfl,
      binaryRegister_execute .mul v (pc + 4) 2 3 1 memory afterRead input output
      (by omega) (by omega) (by omega)]
    change some (state original (pc + 4 + 1) memory
      (put afterRead 2 (afterRead 3 * afterRead 1 % 2 ^ (v + 1))) input output) =
      some (state original (pc + 4 + 1) memory afterDouble input output)
    have hthree : afterRead 3 = pointer := by simp [afterRead]
    rw [hthree, hsRead.2, Nat.mul_comm, Nat.mod_eq_of_lt hdouble]
  rw [hmul]
  simp only [Option.bind_some]
  have hload : execute (v + 1) [.load 11 5]
      (state original (pc + 4 + 1) memory afterDouble input output) =
      some (state original (pc + 4 + 1 + 1) memory afterLoad input output) := by
    have h5 : 5 % 2 ^ (v + 1) = 5 := Nat.mod_eq_of_lt (by omega)
    have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
    have hset11 := set_odd v memory afterDouble 11 (memory pointer)
      (by decide) (by omega)
    have haddress : merge memory afterDouble 5 = 2 * pointer := by
      simpa [afterDouble] using merge_odd memory afterDouble 2
    have hread : merge memory afterDouble (2 * pointer) = memory pointer :=
      merge_even memory afterDouble pointer
    have hset : setCell (v + 1) (merge memory afterDouble) 11 (memory pointer) =
        merge memory (put afterDouble 5 (memory pointer)) := by
      simpa [Nat.mod_eq_of_lt hloaded, Nat.add_div, Nat.mul_div_right] using hset11
    simp only [execute, Instr.effect, state, h5, haddress,
      Nat.mod_eq_of_lt hdouble, hread, hset, Option.bind_some]
    rfl
  rw [hload]
  simp only [Option.bind_some]
  rw [writeCell_execute v (pc + 4 + 1 + 1) target memory afterLoad input output
    hcapacity hsLoad.1 hsLoad.2]
  have hmemory : setCell v memory target (memory pointer) =
      setCell v memory target (memory (memory (addressCell % 2 ^ v))) := by
    rfl
  rw [hmemory]
  congr 2
  change put (put afterLoad 2 (2 * (target % 2 ^ v))) 5
      (afterLoad 5 % 2 ^ v) = nextScratch
  rw [show afterLoad 5 = memory pointer by simp [afterLoad],
    Nat.mod_eq_of_lt (hnormal pointer)]

theorem body_store (v pc addressCell valueCell : Nat) (memory scratch : Nat → Nat)
    (input output : List Nat) (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hscratch : CompilerScratch v scratch) (hnormal : Normalized v memory) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (body (.store addressCell valueCell))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.store addressCell valueCell)).length)
          (setCell v memory (memory (addressCell % 2 ^ v))
            (memory (valueCell % 2 ^ v))) nextScratch input output) := by
  rcases hscratch with ⟨hmask, htwo⟩
  let pointer := memory (addressCell % 2 ^ v)
  let value := memory (valueCell % 2 ^ v)
  let afterPointer := put (put scratch 2 (2 * (addressCell % 2 ^ v))) 3 pointer
  let afterValue := put (put afterPointer 2 (2 * (valueCell % 2 ^ v))) 5 value
  let afterDouble := put afterValue 2 (2 * pointer)
  let nextScratch := put afterDouble 5 value
  have hpointer : pointer < 2 ^ v := hnormal _
  have hvalue : value < 2 ^ v := hnormal _
  have hdouble : 2 * pointer < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hsPointer : CompilerScratch v afterPointer := compilerScratch_put v _
    (compilerScratch_put v scratch ⟨hmask, htwo⟩ 2 _ (by omega)) 3 _ (by omega)
  have hsValue : CompilerScratch v afterValue := compilerScratch_put v _
    (compilerScratch_put v afterPointer hsPointer 2 _ (by omega)) 5 _ (by omega)
  have hsDouble : CompilerScratch v afterDouble :=
    compilerScratch_put v afterValue hsValue 2 _ (by omega)
  have hsNext : CompilerScratch v nextScratch :=
    compilerScratch_put v afterDouble hsDouble 5 _ (by omega)
  refine ⟨nextScratch, hsNext, ?_, ?_⟩
  · intro index hindex
    have h2 : index ≠ 2 := by omega
    have h3 : index ≠ 3 := by omega
    have h5 : index ≠ 5 := by omega
    simp [nextScratch, afterDouble, afterValue, afterPointer, put, h2, h3, h5]
  rw [show body (.store addressCell valueCell) =
      readCell 7 addressCell ++ readCell 11 valueCell ++ [.mul 5 7 3] ++
        [.and 11 11 1] ++ [.store 5 11] by rfl,
    execute_append, execute_append, execute_append, execute_append,
    readCell_execute v pc addressCell 3 memory scratch input output hcapacity
      (by omega) hmask htwo hnormal]
  simp only [Option.bind_some]
  rw [readCell_execute v (pc + 4) valueCell 5 memory afterPointer input output
    hcapacity (by omega) hsPointer.1 hsPointer.2 hnormal]
  simp only [Option.bind_some]
  have hmul : execute (v + 1) [.mul 5 7 3]
      (state original (pc + 4 + 4) memory afterValue input output) =
      some (state original (pc + 4 + 4 + 1) memory afterDouble input output) := by
    rw [show [.mul 5 7 3] =
        [BinaryKind.instruction .mul (2 * 2 + 1) (2 * 3 + 1) (2 * 1 + 1)] by
          rfl,
      binaryRegister_execute .mul v (pc + 4 + 4) 2 3 1 memory afterValue
        input output (by omega) (by omega) (by omega)]
    change some (state original (pc + 4 + 4 + 1) memory
      (put afterValue 2 (afterValue 3 * afterValue 1 % 2 ^ (v + 1))) input output) =
      some (state original (pc + 4 + 4 + 1) memory afterDouble input output)
    have hthree : afterValue 3 = pointer := by simp [afterValue, afterPointer]
    rw [hthree, hsValue.2, Nat.mul_comm, Nat.mod_eq_of_lt hdouble]
  rw [hmul]
  simp only [Option.bind_some]
  have hand : execute (v + 1) [.and 11 11 1]
      (state original (pc + 4 + 4 + 1) memory afterDouble input output) =
      some (state original (pc + 4 + 4 + 1 + 1) memory nextScratch input output) := by
    rw [show [.and 11 11 1] =
        [BinaryKind.instruction .and (2 * 5 + 1) (2 * 5 + 1) (2 * 0 + 1)] by
          rfl,
      binaryRegister_execute .and v (pc + 4 + 4 + 1) 5 5 0 memory afterDouble
        input output (by omega) (by omega) (by omega)]
    change some (state original (pc + 4 + 4 + 1 + 1) memory
      (put afterDouble 5 (Nat.land (afterDouble 5) (afterDouble 0) % 2 ^ (v + 1)))
        input output) =
      some (state original (pc + 4 + 4 + 1 + 1) memory nextScratch input output)
    have hfive : afterDouble 5 = value := by simp [afterDouble, afterValue]
    have hzero : afterDouble 0 = 2 ^ v - 1 := hsDouble.1
    have hland : Nat.land value (2 ^ v - 1) = value := by
      change (value &&& (2 ^ v - 1)) = value
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hvalue]
    rw [hfive, hzero, hland, Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le hvalue (Nat.pow_le_pow_right (by decide) (by omega)))]
  rw [hand]
  simp only [Option.bind_some]
  have hstore : execute (v + 1) [.store 5 11]
      (state original (pc + 4 + 4 + 1 + 1) memory nextScratch input output) =
      some (state original (pc + 4 + 4 + 1 + 1 + 1)
        (setCell v memory pointer value) nextScratch input output) := by
    have h5 : 5 % 2 ^ (v + 1) = 5 := Nat.mod_eq_of_lt (by omega)
    have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
    have haddress : merge memory nextScratch 5 = 2 * pointer := by
      simpa [nextScratch, afterDouble] using merge_odd memory nextScratch 2
    have hstored : merge memory nextScratch 11 = value := by
      simpa [nextScratch] using merge_odd memory nextScratch 5
    have hset : setCell (v + 1) (merge memory nextScratch) (2 * pointer) value =
        merge (setCell v memory pointer value) nextScratch := by
      simpa [Nat.mod_eq_of_lt hpointer, Nat.mod_eq_of_lt hvalue] using
        set_virtual v memory nextScratch pointer value
    simp only [execute, Instr.effect, state, h5, h11, haddress, hstored, hset,
      Option.bind_some]
  rw [hstore]
  congr 2

/-- Original input length is read independently of the sequential cursor. -/
theorem body_inputLength (v pc address : Nat) (memory scratch : Nat → Nat)
    (input output : List Nat) (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hscratch : CompilerScratch v scratch) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (body (.inputLength address))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.inputLength address)).length)
          (setCell v memory address original.length) nextScratch input output) := by
  simpa only [body, List.singleton_append, List.length_cons, execute, Instr.effect, state] using
    (body_set (original := original) v pc address original.length memory scratch
      input output hcapacity hscratch)

/-- Indexed input reads use the virtual word index and retain both input views. -/
theorem body_inputLoad (v pc target addressCell : Nat) (memory scratch : Nat → Nat)
    (input output : List Nat) (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hscratch : CompilerScratch v scratch) (hnormal : Normalized v memory) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (body (.inputLoad target addressCell))
        (state original pc memory scratch input output) =
        some (state original (pc + (body (.inputLoad target addressCell)).length)
          (setCell v memory target (original[memory (addressCell % 2 ^ v)]?.getD 0))
          nextScratch input output) := by
  let pointer := memory (addressCell % 2 ^ v)
  let afterRead := put (put scratch 2 (2 * (addressCell % 2 ^ v))) 3 pointer
  let value := original[pointer]?.getD 0
  have hsRead : CompilerScratch v afterRead := compilerScratch_put v _
    (compilerScratch_put v scratch hscratch 2 _ (by omega)) 3 _ (by omega)
  have hhigh : ScratchPreservedFrom 6 scratch afterRead := by
    intro index hindex
    simp [afterRead, put, show index ≠ 2 by omega, show index ≠ 3 by omega]
  rcases body_set (original := original) v (pc + 4) target value memory afterRead
      input output hcapacity hsRead with ⟨nextScratch, hsNext, hsHigh, hset⟩
  refine ⟨nextScratch, hsNext, hhigh.trans hsHigh, ?_⟩
  rw [show body (.inputLoad target addressCell) =
      readCell 7 addressCell ++ ([.inputLoad 11 7] ++ writeCell target) by rfl,
    execute_append, readCell_execute v pc addressCell 3 memory scratch input output
      hcapacity (by omega) hscratch.1 hscratch.2 hnormal]
  simp only [Option.bind_some]
  change execute (v + 1) ([.inputLoad 11 7] ++ writeCell target)
      (state original (pc + 4) memory afterRead input output) = _
  have h7 : 7 % 2 ^ (v + 1) = 7 := Nat.mod_eq_of_lt (by omega)
  have hindex : pointer < 2 ^ (v + 1) :=
    (hnormal _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hlookup : merge memory afterRead 7 % 2 ^ (v + 1) = pointer := by
    rw [show merge memory afterRead 7 = afterRead 3 from merge_odd memory afterRead 3,
      show afterRead 3 = pointer by simp [afterRead], Nat.mod_eq_of_lt hindex]
  have htail : execute (v + 1) ([.inputLoad 11 7] ++ writeCell target)
      (state original (pc + 4) memory afterRead input output) =
      execute (v + 1) (body (.set target value))
        (state original (pc + 4) memory afterRead input output) := by
    simp only [body, List.singleton_append, execute, Instr.effect, state, h7, hlookup]
    rfl
  rw [htail, hset]
  congr 2

/-- The only body-to-branch datum is the value tested by `jzero`; every
other translated instruction needs no scratch postcondition beyond the two
compiler constants. -/
def BranchReady (v : Nat) (i : Instr) (source : State)
    (scratch : Nat → Nat) : Prop :=
  match i with
  | .jzero address _ => scratch 5 = source.mem (address % 2 ^ v)
  | _ => True

/-- Uniform straight-line simulation of every source instruction that has a
successor state. Jumps deliberately leave the physical counter at the end of
the empty body; the following branch slots perform the source control flow. -/
theorem body_effect {v physicalPc : Nat} {i : Instr} {source next : State}
    {scratch : Nat → Nat} (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hscratch : CompilerScratch v scratch) (hnormal : Normalized v source.mem)
    (heffect : i.effect v source = some next) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧ BranchReady v i source nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (body i)
        (state source.input physicalPc source.mem scratch source.inp source.out) =
        some (state next.input (physicalPc + (body i).length) next.mem nextScratch
          next.inp next.out) := by
  cases i with
  | set address value =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_set v physicalPc address value source.mem scratch source.inp source.out
        hcapacity hscratch with ⟨nextScratch, hsNext, hhigh, hrun⟩
      exact ⟨nextScratch, hsNext, trivial, hhigh, hrun⟩
  | load target addressCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      let pointer := source.mem (addressCell % 2 ^ v)
      have hpointer : pointer < 2 ^ v := hnormal _
      rcases body_load v physicalPc target addressCell source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch, hsNext, hhigh, hrun⟩
      refine ⟨nextScratch, hsNext, trivial, hhigh, ?_⟩
      simpa [pointer, Nat.mod_eq_of_lt hpointer] using hrun
  | store addressCell valueCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_store v physicalPc addressCell valueCell source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch, hsNext, hhigh, hrun⟩
      exact ⟨nextScratch, hsNext, trivial, hhigh, hrun⟩
  | add target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .add v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch, hsNext, hhigh, hrun⟩
      exact ⟨nextScratch, hsNext, trivial, hhigh, hrun⟩
  | sub target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .sub v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch, hsNext, hhigh, hrun⟩
      exact ⟨nextScratch, hsNext, trivial, hhigh, hrun⟩
  | mul target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .mul v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch, hsNext, hhigh, hrun⟩
      exact ⟨nextScratch, hsNext, trivial, hhigh, hrun⟩
  | div target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .div v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch, hsNext, hhigh, hrun⟩
      exact ⟨nextScratch, hsNext, trivial, hhigh, hrun⟩
  | and target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .and v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch, hsNext, hhigh, hrun⟩
      exact ⟨nextScratch, hsNext, trivial, hhigh, hrun⟩
  | shiftl target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_binary .shiftl v physicalPc target left right source.mem scratch source.inp
        source.out hcapacity hscratch hnormal with ⟨nextScratch, hsNext, hhigh, hrun⟩
      exact ⟨nextScratch, hsNext, trivial, hhigh, hrun⟩
  | not target sourceCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_not v physicalPc target sourceCell source.mem scratch source.inp source.out
        hcapacity hscratch hnormal with ⟨nextScratch, hsNext, hhigh, hrun⟩
      exact ⟨nextScratch, hsNext, trivial, hhigh, hrun⟩
  | jump target =>
      simp only [Instr.effect] at heffect
      cases heffect
      exact ⟨scratch, hscratch, trivial, scratchPreservedFrom_refl 6 scratch,
        by simp [body, execute]⟩
  | jzero address target =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_jzero v physicalPc address target source.mem scratch source.inp source.out
        hcapacity hscratch hnormal with ⟨nextScratch, hsNext, hhigh, hrun, hready⟩
      exact ⟨nextScratch, hsNext, hready, hhigh, hrun⟩
  | jeof target =>
      simp only [Instr.effect] at heffect
      cases heffect
      exact ⟨scratch, hscratch, trivial, scratchPreservedFrom_refl 6 scratch,
        by simp [body, execute]⟩
  | inputLength address =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_inputLength v physicalPc address source.mem scratch source.inp source.out
        hcapacity hscratch with ⟨nextScratch, hsNext, hhigh, hrun⟩
      exact ⟨nextScratch, hsNext, trivial, hhigh, hrun⟩
  | inputLoad target addressCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_inputLoad v physicalPc target addressCell source.mem scratch
        source.inp source.out hcapacity hscratch hnormal with
        ⟨nextScratch, hsNext, hhigh, hrun⟩
      refine ⟨nextScratch, hsNext, trivial, hhigh, ?_⟩
      simpa only [Nat.mod_eq_of_lt (hnormal _)] using hrun
  | halt =>
      simp only [Instr.effect] at heffect
      contradiction
  | read address =>
      simp only [Instr.effect] at heffect
      cases hinput : source.inp with
      | nil => simp [hinput] at heffect
      | cons value rest =>
          simp [hinput] at heffect
          cases heffect
          rcases body_read v physicalPc address value rest source.mem scratch source.out
            hcapacity hscratch with ⟨nextScratch, hsNext, hhigh, hrun⟩
          exact ⟨nextScratch, hsNext, trivial, hhigh, hrun⟩
  | write address =>
      simp only [Instr.effect] at heffect
      cases heffect
      rcases body_write v physicalPc address source.mem scratch source.inp source.out
        hcapacity hscratch hnormal with ⟨nextScratch, hsNext, hhigh, hrun⟩
      refine ⟨nextScratch, hsNext, trivial, hhigh, ?_⟩
      simpa [Nat.mod_eq_of_lt (hnormal _)] using hrun

/-- Completing the fixed body padding preserves the simulated successor and
places the physical counter at branch slot sixteen. -/
theorem paddedBody_effect {v physicalPc : Nat} {i : Instr} {source next : State}
    {scratch : Nat → Nat} (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hscratch : CompilerScratch v scratch) (hnormal : Normalized v source.mem)
    (heffect : i.effect v source = some next) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧ BranchReady v i source nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (paddedBody i)
        (state source.input physicalPc source.mem scratch source.inp source.out) =
        some (state next.input (physicalPc + 16) next.mem nextScratch next.inp next.out) := by
  rcases body_effect (physicalPc := physicalPc) hcapacity hscratch hnormal heffect with
    ⟨bodyScratch, hsBody, hready, hbodyHigh, hbody⟩
  rcases padding_execute v (16 - (body i).length)
      (physicalPc + (body i).length) next.mem bodyScratch next.inp next.out
      hcapacity hsBody with ⟨nextScratch, hsNext, hfive, hpaddingHigh, hpadding⟩
  refine ⟨nextScratch, hsNext, ?_, hbodyHigh.trans hpaddingHigh, ?_⟩
  · cases i <;> simp only [BranchReady] at hready ⊢
    all_goals try trivial
    rw [hfive]
    exact hready
  · rw [paddedBody, execute_append, hbody, Option.bind_some, hpadding]
    congr 2
    have := body_length_le i
    omega

/-- The padded body is a real sixteen-step prefix of the compiled block. -/
theorem run_paddedBody {v : Nat} {program : Program} {i : Instr}
    {source next : State} {scratch : Nat → Nat}
    (hcapacity : 16 ≤ 2 ^ (v + 1)) (hfetch : program[source.pc]? = some i)
    (hscratch : CompilerScratch v scratch) (hnormal : Normalized v source.mem)
    (heffect : i.effect v source = some next) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧ BranchReady v i source nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      run (v + 1) (compile program) 16
        (state source.input (location source.pc) source.mem scratch source.inp source.out) =
        some (state next.input (location source.pc + 16) next.mem nextScratch
          next.inp next.out) := by
  have hlinear : ∀ instruction ∈ paddedBody i, StraightLine instruction := by
    intro instruction hinstruction
    simp only [paddedBody, List.mem_append, List.mem_replicate] at hinstruction
    rcases hinstruction with hinstruction | ⟨_, rfl⟩
    · exact body_straightLine i instruction hinstruction
    · trivial
  have hpaddedFetch : ∀ k, k < (paddedBody i).length →
      (compile program)[(state source.input (location source.pc) source.mem scratch
        source.inp source.out).pc + k]? = (paddedBody i)[k]? := by
    intro k hk
    exact compile_get_paddedBody program source.pc i hfetch k (by simpa using hk)
  rw [show 16 = (paddedBody i).length by simp,
    run_eq_execute (v + 1) (compile program) (paddedBody i)
      (state source.input (location source.pc) source.mem scratch source.inp source.out)
      hlinear hpaddedFetch]
  simpa using (paddedBody_effect (physicalPc := location source.pc)
    hcapacity hscratch hnormal heffect)

/-- The branch suffix performs exactly the source control-flow update. Most
instructions use one physical jump; a nonzero conditional uses its second
slot and therefore takes two steps. -/
theorem run_branch {v : Nat} {program : Program} {i : Instr}
    {source next : State} {scratch : Nat → Nat}
    (hcapacity : 16 ≤ 2 ^ (v + 1)) (hfetch : program[source.pc]? = some i)
    (hready : BranchReady v i source scratch)
    (heffect : i.effect v source = some next) :
    ∃ cost, 1 ≤ cost ∧ cost ≤ 2 ∧
      run (v + 1) (compile program) cost
        (state next.input (location source.pc + 16) next.mem scratch next.inp next.out) =
        some (state next.input (location next.pc) next.mem scratch next.inp next.out) := by
  have hfirst := compile_get_branch program source.pc i hfetch 0 (by omega)
  have hsecond := compile_get_branch program source.pc i hfetch 1 (by omega)
  have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
  cases i with
  | set address value =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | load target addressCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | store addressCell valueCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | add target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | sub target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | mul target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | div target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | and target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | shiftl target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | not target sourceCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | jump target =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | jzero address target =>
      simp only [Instr.effect] at heffect
      cases heffect
      simp only [BranchReady] at hready
      have htest : merge source.mem scratch 11 = source.mem (address % 2 ^ v) := by
        calc
          merge source.mem scratch 11 = scratch 5 := by
            simpa using merge_odd source.mem scratch 5
          _ = source.mem (address % 2 ^ v) := hready
      by_cases hzero : source.mem (address % 2 ^ v) = 0
      · refine ⟨1, by omega, by omega, ?_⟩
        simp [run, step, hfirst, branch, Instr.effect, state, h11, htest, hzero]
      · refine ⟨2, by omega, by omega, ?_⟩
        simp [run, step, hfirst, hsecond, branch, Instr.effect, state, h11,
          htest, hzero]
  | jeof target =>
      simp only [Instr.effect] at heffect
      cases heffect
      cases hinput : source.inp with
      | nil =>
          refine ⟨1, by omega, by omega, ?_⟩
          simp [run, step, hfirst, branch, Instr.effect, state, hinput]
      | cons value rest =>
          refine ⟨2, by omega, by omega, ?_⟩
          simp [run, step, hfirst, hsecond, branch, Instr.effect, state, hinput]
  | inputLength address =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | inputLoad target addressCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | halt =>
      simp only [Instr.effect] at heffect
      contradiction
  | read address =>
      simp only [Instr.effect] at heffect
      cases hinput : source.inp with
      | nil => simp [hinput] at heffect
      | cons value rest =>
          simp [hinput] at heffect
          cases heffect
          refine ⟨1, by omega, by omega, ?_⟩
          simp [run, step, hfirst, branch, Instr.effect, state]
  | write address =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]

/-- One successful virtual RAM step is simulated by at most eighteen
physical instructions, with no assumption that any virtual address is free. -/
theorem simulation_step {v : Nat} {program : Program} {source next physical : State}
    (hcapacity : 16 ≤ 2 ^ (v + 1)) (hsimulates : Simulates v source physical)
    (hstep : step v program source = some next) :
    ∃ cost nextPhysical,
      cost ≤ 18 ∧ run (v + 1) (compile program) cost physical = some nextPhysical ∧
      Simulates v next nextPhysical := by
  rcases hsimulates with ⟨scratch, hscratch, hnormal, rfl⟩
  simp only [step] at hstep
  cases hfetch : program[source.pc]? with
  | none => simp [hfetch] at hstep
  | some instruction =>
      rw [hfetch] at hstep
      simp only [Option.bind_some] at hstep
      rcases run_paddedBody hcapacity hfetch hscratch hnormal hstep with
        ⟨bodyScratch, hsBody, hready, hbodyHigh, hbody⟩
      rcases run_branch hcapacity hfetch hready hstep with
        ⟨branchCost, hcostPositive, hcost, hbranch⟩
      let nextPhysical := state next.input (location next.pc) next.mem bodyScratch next.inp next.out
      refine ⟨16 + branchCost, nextPhysical, by omega, ?_, ?_⟩
      · rw [run_add, hbody, Option.bind_some, hbranch]
      · exact ⟨bodyScratch, hsBody, normalized_effect hnormal hstep, rfl⟩

/-- A finite successful source run lifts compositionally, with at most the
constant factor eighteen in executed instructions. -/
theorem simulation_run {v : Nat} {program : Program} {time : Nat}
    {source next physical : State} (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hsimulates : Simulates v source physical)
    (hrun : run v program time source = some next) :
    ∃ cost nextPhysical,
      cost ≤ 18 * time ∧
      run (v + 1) (compile program) cost physical = some nextPhysical ∧
      Simulates v next nextPhysical := by
  induction time generalizing source next physical with
  | zero =>
      simp only [run] at hrun
      cases hrun
      exact ⟨0, physical, by omega, by simp [run], hsimulates⟩
  | succ time ih =>
      simp only [run] at hrun
      cases hsourceStep : step v program source with
      | none => simp [hsourceStep] at hrun
      | some intermediate =>
          rw [hsourceStep] at hrun
          simp only [Option.bind_some] at hrun
          rcases simulation_step hcapacity hsimulates hsourceStep with
            ⟨firstCost, intermediatePhysical, hfirstCost, hfirstRun, hfirstSimulates⟩
          rcases ih hfirstSimulates hrun with
            ⟨restCost, nextPhysical, hrestCost, hrestRun, hnextSimulates⟩
          refine ⟨firstCost + restCost, nextPhysical, by omega, ?_, hnextSimulates⟩
          rw [run_add, hfirstRun, Option.bind_some, hrestRun]

theorem simulation_start (v : Nat) (program : Program) (input : List Nat)
    (hcapacity : 16 ≤ 2 ^ (v + 1)) :
    ∃ physical,
      run (v + 1) (compile program) 4 (initState input) = some physical ∧
      Simulates v (initState input) physical := by
  let scratch := put (put (fun _ => 0) 1 2) 0 (2 ^ v - 1)
  let physical := state input 4 (fun _ => 0) scratch input []
  refine ⟨physical, compile_start v program input hcapacity, ?_⟩
  refine ⟨scratch, ?_, normalized_init v input, ?_⟩
  · constructor <;> simp [scratch]
  · simp [physical, initState, location]

/-- A simulated source state input whose next step halts can be advanced to a
physical halt in at most sixteen preparation steps. This covers explicit
`halt`, exhausted reads, and counters outside the program. -/
theorem simulation_halt {v : Nat} {program : Program} {source physical : State}
    (hcapacity : 16 ≤ 2 ^ (v + 1)) (hsimulates : Simulates v source physical)
    (hhalt : step v program source = none) :
    ∃ cost final,
      cost ≤ 16 ∧ run (v + 1) (compile program) cost physical = some final ∧
      step (v + 1) (compile program) final = none ∧ final.out = source.out := by
  rcases hsimulates with ⟨scratch, hscratch, hnormal, rfl⟩
  simp only [step] at hhalt
  cases hfetch : program[source.pc]? with
  | none =>
      have hcompiled : (compile program)[location source.pc]? = none := by
        have hcompiledAtZero := compile_get program source.pc 0 (by omega)
        simpa [hfetch] using hcompiledAtZero
      refine ⟨0, state source.input (location source.pc) source.mem scratch source.inp source.out,
        by omega, by simp [run], ?_, rfl⟩
      simp [step, state, hcompiled]
  | some instruction =>
      rw [hfetch] at hhalt
      simp only [Option.bind_some] at hhalt
      cases instruction with
      | halt =>
          let padding := List.replicate 16 (Instr.set 5 0)
          have hpaddingDef : paddedBody Instr.halt = padding := by
            rfl
          have hlinear : ∀ i ∈ padding, StraightLine i := by
            intro i hi
            simp only [padding, List.mem_replicate] at hi
            rcases hi with ⟨_, rfl⟩
            trivial
          have hprefix : ∀ k, k < padding.length →
              (compile program)[location source.pc + k]? = padding[k]? := by
            intro k hk
            rw [← hpaddingDef]
            exact compile_get_paddedBody program source.pc Instr.halt hfetch k
              (by simpa [padding] using hk)
          rcases padding_execute v 16 (location source.pc) source.mem scratch
              source.inp source.out hcapacity hscratch with
            ⟨nextScratch, hsNext, hfive, hpaddingHigh, hpadding⟩
          let final := state source.input (location source.pc + 16) source.mem nextScratch
            source.inp source.out
          have hrun : run (v + 1) (compile program) 16
              (state source.input (location source.pc) source.mem scratch source.inp source.out) =
              some final := by
            rw [show 16 = padding.length by simp [padding],
              run_eq_execute (v + 1) (compile program) padding
                (state source.input (location source.pc) source.mem scratch source.inp source.out)
                hlinear hprefix]
            exact hpadding
          have hbranch := compile_get_branch program source.pc Instr.halt hfetch 0 (by omega)
          have hfinalHalt : step (v + 1) (compile program) final = none := by
            simp [step, final, hbranch, branch, Instr.effect, state]
          exact ⟨16, final, by omega, hrun, hfinalHalt, rfl⟩
      | read address =>
          cases hinput : source.inp with
          | nil =>
              have hcompiled := compile_get_paddedBody program source.pc (.read address)
                hfetch 0 (by omega)
              have hcompiledRead :
                  (compile program)[location source.pc]? = some (.read 11) := by
                simpa [paddedBody, body] using hcompiled
              refine ⟨0, state source.input (location source.pc) source.mem scratch [] source.out,
                by omega, ?_, ?_, rfl⟩
              · simp [run, hinput]
              · simp [step, hcompiledRead, Instr.effect, state]
          | cons value rest =>
              simp [Instr.effect, hinput] at hhalt
      | set address value => simp [Instr.effect] at hhalt
      | load target addressCell => simp [Instr.effect] at hhalt
      | store addressCell valueCell => simp [Instr.effect] at hhalt
      | add target left right => simp [Instr.effect] at hhalt
      | sub target left right => simp [Instr.effect] at hhalt
      | mul target left right => simp [Instr.effect] at hhalt
      | div target left right => simp [Instr.effect] at hhalt
      | and target left right => simp [Instr.effect] at hhalt
      | shiftl target left right => simp [Instr.effect] at hhalt
      | not target sourceCell => simp [Instr.effect] at hhalt
      | jump target => simp [Instr.effect] at hhalt
      | jzero address target => simp [Instr.effect] at hhalt
      | write address => simp [Instr.effect] at hhalt
      | jeof target => simp [Instr.effect] at hhalt
      | inputLength address => simp [Instr.effect] at hhalt
      | inputLoad target addressCell => simp [Instr.effect] at hhalt

/-- Every Lax808846 program has an exact-output simulation at one extra bit
of width. The bound includes both machines' fetched terminal instructions.
No bound on the original input length or its entries is required. -/
theorem runsTo_compile {v : Nat} {program : Program} {input output : List Nat}
    {time : Nat} (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hruns : RunsTo v program input output time) :
    ∃ physicalTime ≤ 18 * time + 21,
      RunsTo (v + 1) (compile program) input output physicalTime := by
  rcases hruns with ⟨sourceSteps, sourceFinal, hsourceRun, hsourceHalt, houtput, htime⟩
  rcases simulation_start v program input hcapacity with
    ⟨physicalStart, hstart, hstartSimulates⟩
  rcases simulation_run hcapacity hstartSimulates hsourceRun with
    ⟨runCost, physicalFinal, hrunCost, hrun, hfinalSimulates⟩
  rcases simulation_halt hcapacity hfinalSimulates hsourceHalt with
    ⟨haltCost, final, hhaltCost, hhaltRun, hphysicalHalt, hfinalOutput⟩
  have hterminal : terminalCost (compile program) final ≤ 1 := by
    unfold terminalCost
    split <;> omega
  refine ⟨4 + runCost + haltCost + terminalCost (compile program) final, by omega,
    4 + runCost + haltCost, final, ?_, hphysicalHalt, ?_, rfl⟩
  · rw [show 4 + runCost + haltCost = 4 + (runCost + haltCost) by omega,
      run_add, hstart, Option.bind_some, run_add, hrun, Option.bind_some, hhaltRun]
  · rw [hfinalOutput, houtput]

end Lax759944Proofs.TapeRamVirtualSimulation
