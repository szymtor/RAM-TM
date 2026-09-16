import Lax759944Proofs.TapeRamVirtualCompiler

namespace Lax759944Proofs.TapeRamVirtualMacros

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualCompiler

/-- Execute a straight-line instruction sequence. The later fetch lemma
connects this fold to `Ram.run` inside the containing compiled program. -/
def execute (w : Nat) : Program → State → Option State
  | [], s => some s
  | i :: rest, s => (i.effect w s).bind (execute w rest)

theorem execute_append (w : Nat) (first second : Program) (s : State) :
    execute w (first ++ second) s =
      (execute w first s).bind (execute w second) := by
  induction first generalizing s with
  | nil => rfl
  | cons i first ih => simp [execute, ih, Option.bind_assoc]

/-- Straight-line instructions may halt (notably on exhausted input), but
cannot move the counter anywhere other than its successor when they run. -/
def StraightLine : Instr → Prop
  | .jump _ | .jzero _ _ | .jeof _ => False
  | _ => True

theorem straightLine_effect_pc (i : Instr) (hlinear : StraightLine i)
    (w : Nat) (s next : State) (heffect : i.effect w s = some next) :
    next.pc = s.pc + 1 := by
  cases i <;> simp only [StraightLine] at hlinear
  all_goals try contradiction
  all_goals simp only [Instr.effect] at heffect
  all_goals try { cases heffect; rfl }
  case read a =>
    cases hi : s.inp.head? with
    | none => rw [hi] at heffect; cases heffect
    | some value => rw [hi] at heffect; cases heffect; rfl

/-- The straight-line proof fold is precisely the real RAM run when the
instructions occur at the current program position. This includes failure
from a halt instruction or exhausted read, rather than assuming success. -/
theorem run_eq_execute (w : Nat) (p code : Program) (s : State)
    (hlinear : ∀ i ∈ code, StraightLine i)
    (hfetch : ∀ k, k < code.length → p[s.pc + k]? = code[k]?) :
    run w p code.length s = execute w code s := by
  induction code generalizing s with
  | nil => rfl
  | cons i code ih =>
    have hfirst : p[s.pc]? = some i := by simpa using hfetch 0 (by simp)
    simp only [List.length_cons, run, step, hfirst, Option.bind_some, execute]
    cases heffect : i.effect w s with
    | none => rfl
    | some next =>
      simp only [Option.bind_some]
      have hpc := straightLine_effect_pc i (hlinear i (by simp)) w s next heffect
      apply ih next
      · intro j hj
        exact hlinear j (by simp [hj])
      · intro k hk
        have := hfetch (k + 1) (by simp; omega)
        simpa [hpc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem run_add (w : Nat) (p : Program) (first second : Nat) (s : State) :
    run w p (first + second) s = (run w p first s).bind (run w p second) := by
  induction first generalizing s with
  | zero => simp [run]
  | succ first ih =>
      simp only [Nat.succ_add, run]
      cases hstep : step w p s with
      | none => rfl
      | some next =>
          simp only [Option.bind_some]
          exact ih next

def put (scratch : Nat → Nat) (index value : Nat) : Nat → Nat :=
  fun a => if a = index then value else scratch a

@[simp] theorem put_same (scratch : Nat → Nat) (index value : Nat) :
    put scratch index value index = value := by simp [put]

@[simp] theorem put_other (scratch : Nat → Nat) (index value a : Nat) (h : a ≠ index) :
    put scratch index value a = scratch a := by simp [put, h]

@[simp] theorem put_overwrite (scratch : Nat → Nat) (index first second : Nat) :
    put (put scratch index first) index second = put scratch index second := by
  funext a
  by_cases ha : a = index <;> simp [put, ha]

/-- The immutable original input and the unread sequential suffix are distinct. -/
def state (original : List Nat) (pc : Nat) (memory scratch : Nat → Nat) (input output : List Nat) : State :=
  ⟨pc, merge memory scratch, original, input, output⟩

variable {original : List Nat}

def Normalized (v : Nat) (memory : Nat → Nat) : Prop :=
  ∀ address, memory address < 2 ^ v

def CompilerScratch (v : Nat) (scratch : Nat → Nat) : Prop :=
  scratch 0 = 2 ^ v - 1 ∧ scratch 1 = 2

def ScratchPreservedFrom (threshold : Nat) (before after : Nat → Nat) : Prop :=
  ∀ index, threshold ≤ index → after index = before index

theorem scratchPreservedFrom_refl (threshold : Nat) (scratch : Nat → Nat) :
    ScratchPreservedFrom threshold scratch scratch := by
  intro index hindex
  rfl

theorem ScratchPreservedFrom.trans {threshold : Nat} {first second third : Nat → Nat}
    (hfirst : ScratchPreservedFrom threshold first second)
    (hsecond : ScratchPreservedFrom threshold second third) :
    ScratchPreservedFrom threshold first third := by
  intro index hindex
  rw [hsecond index hindex, hfirst index hindex]

theorem scratchPreservedFrom_put (threshold : Nat) (scratch : Nat → Nat)
    (index value : Nat) (hindex : index < threshold) :
    ScratchPreservedFrom threshold scratch (put scratch index value) := by
  intro other hother
  simp [put]
  omega

theorem normalized_setCell (v : Nat) (memory : Nat → Nat)
    (h : Normalized v memory) (address value : Nat) :
    Normalized v (setCell v memory address value) := by
  intro a
  simp only [setCell]
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos v)
  · exact h a

theorem compilerScratch_put (v : Nat) (scratch : Nat → Nat)
    (h : CompilerScratch v scratch) (index value : Nat) (hindex : 2 ≤ index) :
    CompilerScratch v (put scratch index value) := by
  rcases h with ⟨hmask, htwo⟩
  constructor <;> simp [put, hmask, htwo] <;> omega

theorem set_odd (v : Nat) (memory scratch : Nat → Nat) (address value : Nat)
    (hodd : address % 2 = 1) (hbound : address < 2 ^ (v + 1)) :
    setCell (v + 1) (merge memory scratch) address value =
      merge memory (put scratch (address / 2) (value % 2 ^ (v + 1))) := by
  have hindex : address / 2 < 2 ^ v := by rw [Nat.pow_succ] at hbound; omega
  have heq : 2 * (address / 2) + 1 = address := by omega
  simpa only [Nat.mod_eq_of_lt hindex, heq, put] using!
    set_scratch v memory scratch (address / 2) value

theorem setRegister_execute (v pc target value : Nat)
    (memory scratch : Nat → Nat) (input output : List Nat)
    (htarget : 2 * target + 1 < 2 ^ (v + 1)) :
    execute (v + 1) [.set (2 * target + 1) value]
      (state original pc memory scratch input output) =
      some (state original (pc + 1) memory
        (put scratch target (value % 2 ^ (v + 1))) input output) := by
  have hmod := Nat.mod_eq_of_lt htarget
  have hset := set_odd v memory scratch (2 * target + 1) value (by omega) htarget
  simp only [execute, state, Instr.effect, hmod, hset, Option.bind_some]
  simpa [Nat.add_div, Nat.mul_div_right]

theorem readRegister_execute (v pc target value : Nat) (rest : List Nat)
    (memory scratch : Nat → Nat) (output : List Nat)
    (htarget : 2 * target + 1 < 2 ^ (v + 1)) :
    execute (v + 1) [.read (2 * target + 1)]
      (state original pc memory scratch (value :: rest) output) =
      some (state original (pc + 1) memory
        (put scratch target (value % 2 ^ (v + 1))) rest output) := by
  have hmod := Nat.mod_eq_of_lt htarget
  have hset := set_odd v memory scratch (2 * target + 1) value (by omega) htarget
  simp only [execute, state, Instr.effect, List.head?_cons, Option.map_some,
    List.tail_cons, hmod, hset, Option.bind_some]
  simpa [Nat.add_div, Nat.mul_div_right]

theorem registerValue (memory scratch : Nat → Nat) (target : Nat) :
    merge memory scratch (2 * target + 1) = scratch target := by
  exact merge_odd _ _ _

inductive BinaryKind
  | add | sub | mul | div | and | shiftl

def BinaryKind.instruction (kind : BinaryKind) (target left right : Nat) : Instr :=
  match kind with
  | .add => .add target left right
  | .sub => .sub target left right
  | .mul => .mul target left right
  | .div => .div target left right
  | .and => .and target left right
  | .shiftl => .shiftl target left right

def BinaryKind.value (kind : BinaryKind) (left right : Nat) : Nat :=
  match kind with
  | .add => left + right
  | .sub => left - right
  | .mul => left * right
  | .div => left / right
  | .and => Nat.land left right
  | .shiftl => left * 2 ^ right

theorem binaryRegister_execute (kind : BinaryKind) (v pc target left right : Nat)
    (memory scratch : Nat → Nat) (input output : List Nat)
    (htarget : 2 * target + 1 < 2 ^ (v + 1))
    (hleft : 2 * left + 1 < 2 ^ (v + 1))
    (hright : 2 * right + 1 < 2 ^ (v + 1)) :
    execute (v + 1) [kind.instruction (2 * target + 1) (2 * left + 1) (2 * right + 1)]
      (state original pc memory scratch input output) =
      some (state original (pc + 1) memory
        (put scratch target (kind.value (scratch left) (scratch right) % 2 ^ (v + 1)))
        input output) := by
  have ht := Nat.mod_eq_of_lt htarget
  have hl := Nat.mod_eq_of_lt hleft
  have hr := Nat.mod_eq_of_lt hright
  have hset := set_odd v memory scratch (2 * target + 1)
    (kind.value (scratch left) (scratch right)) (by omega) htarget
  cases kind <;> simp only [execute, BinaryKind.instruction, BinaryKind.value,
    state, Instr.effect, ht, hl, hr, merge_odd, Option.bind_some]
  all_goals simpa [BinaryKind.value, Nat.add_div, Nat.mul_div_right] using hset

theorem body_straightLine (i : Instr) : ∀ j ∈ body i, StraightLine j := by
  cases i <;> simp [body, readCell, writeCell, StraightLine]

/-- Padding changes only the temporary address register. In particular it
preserves the branch-test register used by the translated `jzero`. -/
theorem padding_execute (v count pc : Nat) (memory scratch : Nat → Nat)
    (input output : List Nat) (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hscratch : CompilerScratch v scratch) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧ nextScratch 5 = scratch 5 ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (List.replicate count (.set 5 0))
        (state original pc memory scratch input output) =
        some (state original (pc + count) memory nextScratch input output) := by
  induction count generalizing pc scratch with
  | zero =>
      exact ⟨scratch, hscratch, rfl, scratchPreservedFrom_refl 6 scratch,
        by simp [execute]⟩
  | succ count ih =>
      let afterSet := put scratch 2 0
      have hsAfter : CompilerScratch v afterSet :=
        compilerScratch_put v scratch hscratch 2 0 (by omega)
      rcases ih (pc := pc + 1) (scratch := afterSet) hsAfter with
        ⟨nextScratch, hsNext, hfive, hhigh, hexecute⟩
      refine ⟨nextScratch, hsNext, ?_, ?_, ?_⟩
      · rw [hfive]
        simp [afterSet]
      · exact (scratchPreservedFrom_put 6 scratch 2 0 (by omega)).trans hhigh
      · rw [List.replicate_succ]
        change execute (v + 1)
          ([Instr.set 5 0] ++ List.replicate count (Instr.set 5 0))
          (state original pc memory scratch input output) = _
        rw [execute_append,
          setRegister_execute v pc 2 0 memory scratch input output (by omega)]
        simp only [Nat.zero_mod, Option.bind_some]
        change execute (v + 1) (List.replicate count (Instr.set 5 0))
          (state original (pc + 1) memory afterSet input output) = _
        rw [hexecute]
        congr 2
        omega

/-- Uniform initialization of the compiler constants preserves all virtual
memory and all adapter scratch except the two designated constant slots. -/
theorem prelude_execute (v pc : Nat) (memory scratch : Nat → Nat)
    (input output : List Nat) (hcapacity : 16 ≤ 2 ^ (v + 1)) :
    execute (v + 1) prelude (state original pc memory scratch input output) =
      some (state original (pc + 4) memory (put (put scratch 1 2) 0 (2 ^ v - 1)) input output) := by
  have h1 : 1 % 2 ^ (v + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : 2 % 2 ^ (v + 1) = 2 := Nat.mod_eq_of_lt (by omega)
  have h3 : 3 % 2 ^ (v + 1) = 3 := Nat.mod_eq_of_lt (by omega)
  have hset1 (sc : Nat → Nat) (value : Nat) :
      setCell (v + 1) (merge memory sc) 1 value =
        merge memory (put sc 0 (value % 2 ^ (v + 1))) :=
    set_odd v memory sc 1 value (by decide) (by omega)
  have hset3 (sc : Nat → Nat) (value : Nat) :
      setCell (v + 1) (merge memory sc) 3 value =
        merge memory (put sc 1 (value % 2 ^ (v + 1))) :=
    set_odd v memory sc 3 value (by decide) (by omega)
  have hread1 (sc : Nat → Nat) : merge memory sc 1 = sc 0 := by simp [merge]
  have hread3 (sc : Nat → Nat) : merge memory sc 3 = sc 1 := by simp [merge]
  have hall : 2 ^ (v + 1) - 1 < 2 ^ (v + 1) := by omega
  have hmask : 2 ^ v - 1 < 2 ^ (v + 1) := by
    have := Nat.two_pow_pos v
    rw [Nat.pow_succ]
    omega
  simp only [execute, prelude, state, Instr.effect, Option.bind_some,
    h1, h2, h3, hset1, hset3, hread1, hread3, put_same, put_overwrite,
    Nat.zero_mod, Nat.sub_zero, Nat.mod_eq_of_lt hall]
  simp [put, half_all_ones, Nat.mod_eq_of_lt hmask]
  apply congrArg (merge memory)
  funext index
  by_cases hindex : index = 0 <;> simp [put, hindex]

/-- The real compiled program initializes the virtual mask in four RAM
steps, starting from the standard all-zero machine state. -/
theorem compile_start (v : Nat) (p : Program) (input : List Nat)
    (hcapacity : 16 ≤ 2 ^ (v + 1)) :
    run (v + 1) (compile p) 4 (initState input) =
      some (state input 4 (fun _ => 0) (put (put (fun _ => 0) 1 2) 0 (2 ^ v - 1)) input []) := by
  have hlinear : ∀ i ∈ prelude, StraightLine i := by simp [prelude, StraightLine]
  have hfetch : ∀ k, k < prelude.length →
      (compile p)[(initState input).pc + k]? = prelude[k]? := by
    intro k hk
    simp [compile, initState, List.getElem?_append, hk]
  change run (v + 1) (compile p) prelude.length (initState input) = _
  rw [run_eq_execute _ _ _ _ hlinear hfetch]
  have hinitial : initState input = state input 0 (fun _ => 0) (fun _ => 0) input [] := by
    simp only [initState, state]
    congr 1
    funext a
    simp [merge]
  rw [hinitial]
  exact prelude_execute v 0 _ _ input [] hcapacity

/-- Exact semantics of the four-instruction virtual-cell read macro.
The two compiler constants are preserved provided the chosen target is
neither of their odd cells; the formula itself covers every odd target. -/
theorem readCell_execute (v pc address target : Nat)
    (memory scratch : Nat → Nat) (input output : List Nat)
    (hcapacity : 16 ≤ 2 ^ (v + 1)) (htarget : 2 * target + 1 < 2 ^ (v + 1))
    (hmask : scratch 0 = 2 ^ v - 1) (htwo : scratch 1 = 2)
    (hnormal : ∀ a, memory a < 2 ^ v) :
    execute (v + 1) (readCell (2 * target + 1) address)
      (state original pc memory scratch input output) =
      some (state original (pc + 4) memory
        (put (put scratch 2 (2 * (address % 2 ^ v))) target (memory (address % 2 ^ v)))
        input output) := by
  have h1 : 1 % 2 ^ (v + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have h3 : 3 % 2 ^ (v + 1) = 3 := Nat.mod_eq_of_lt (by omega)
  have h5 : 5 % 2 ^ (v + 1) = 5 := Nat.mod_eq_of_lt (by omega)
  have hset5 (sc : Nat → Nat) (value : Nat) :
      setCell (v + 1) (merge memory sc) 5 value =
        merge memory (put sc 2 (value % 2 ^ (v + 1))) :=
    set_odd v memory sc 5 value (by decide) (by omega)
  have hsetTarget (sc : Nat → Nat) (value : Nat) :
      setCell (v + 1) (merge memory sc) (2 * target + 1) value =
        merge memory (put sc target (value % 2 ^ (v + 1))) := by
    simpa [Nat.add_div, Nat.mul_div_right] using
      set_odd v memory sc (2 * target + 1) value (by omega) htarget
  have hread1 (sc : Nat → Nat) : merge memory sc 1 = sc 0 := by simp [merge]
  have hread3 (sc : Nat → Nat) : merge memory sc 3 = sc 1 := by simp [merge]
  have hread5 (sc : Nat → Nat) : merge memory sc 5 = sc 2 := by simp [merge]
  have hdouble := Nat.mod_eq_of_lt (even_address_lt v address)
  have hvalue : memory (address % 2 ^ v) < 2 ^ (v + 1) :=
    Nat.lt_of_lt_of_le (hnormal _) (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [execute, readCell, state, Instr.effect, Option.bind_some,
    h1, h3, h5, hset5, hsetTarget, hread1, hread3, hread5, put_same, put_overwrite]
  congr 2
  simp [put, hmask, htwo, mod_physical_virtual,
    Nat.mul_comm (address % 2 ^ v) 2, hdouble, merge_even, Nat.mod_eq_of_lt hvalue]

/-- Exact write-macro semantics: scratch writes stay in odd cells, and
the final even-cell write agrees with virtual truncation of the result. -/
theorem writeCell_execute (v pc address : Nat)
    (memory scratch : Nat → Nat) (input output : List Nat)
    (hcapacity : 16 ≤ 2 ^ (v + 1))
    (hmask : scratch 0 = 2 ^ v - 1) (htwo : scratch 1 = 2) :
    execute (v + 1) (writeCell address) (state original pc memory scratch input output) =
      some (state original (pc + 5) (setCell v memory address (scratch 5))
        (put (put scratch 2 (2 * (address % 2 ^ v))) 5 (scratch 5 % 2 ^ v))
        input output) := by
  have h1 : 1 % 2 ^ (v + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have h3 : 3 % 2 ^ (v + 1) = 3 := Nat.mod_eq_of_lt (by omega)
  have h5 : 5 % 2 ^ (v + 1) = 5 := Nat.mod_eq_of_lt (by omega)
  have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
  have hset5 (sc : Nat → Nat) (value : Nat) :
      setCell (v + 1) (merge memory sc) 5 value =
        merge memory (put sc 2 (value % 2 ^ (v + 1))) :=
    set_odd v memory sc 5 value (by decide) (by omega)
  have hset11 (sc : Nat → Nat) (value : Nat) :
      setCell (v + 1) (merge memory sc) 11 value =
        merge memory (put sc 5 (value % 2 ^ (v + 1))) :=
    set_odd v memory sc 11 value (by decide) (by omega)
  have hread1 (sc : Nat → Nat) : merge memory sc 1 = sc 0 := by simp [merge]
  have hread3 (sc : Nat → Nat) : merge memory sc 3 = sc 1 := by simp [merge]
  have hread5 (sc : Nat → Nat) : merge memory sc 5 = sc 2 := by simp [merge]
  have hread11 (sc : Nat → Nat) : merge memory sc 11 = sc 5 := by simp [merge]
  have hdouble := Nat.mod_eq_of_lt (even_address_lt v address)
  have hsmall (value : Nat) : value % 2 ^ v < 2 ^ (v + 1) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos v))
      (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [execute, writeCell, state, Instr.effect, Option.bind_some,
    h1, h3, h5, h11, hset5, hset11, hread1, hread3, hread5, hread11,
    put_same, put_overwrite]
  simp [put, hmask, htwo, mod_physical_virtual,
    Nat.mul_comm (address % 2 ^ v) 2, hdouble, Nat.mod_eq_of_lt (hsmall _), set_virtual]

end Lax759944Proofs.TapeRamVirtualMacros
