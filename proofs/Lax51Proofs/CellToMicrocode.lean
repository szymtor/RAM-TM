import Lax51Proofs.Microcode
import Lax51.RamPolytime
import Lax51.TuringRamEquivalence

/-!
Translation from the current cell-to-cell RAM to the proof-internal
accumulator microcode. Each instruction occupies three slots. All addresses
and the word width are preserved: no scratch memory is reserved. Only the
microcode accumulator, represented by a Turing work tape, is additional.
-/

namespace Lax51Proofs.CellToMicrocode

abbrev Block := Microcode.Instr × Microcode.Instr × Microcode.Instr

def lower : Lax13.Ram.Instr → Block
  | .set a n => (.load (.lit n), .store a, .load (.lit 0))
  | .load a b => (.load (.ind b), .store a, .load (.lit 0))
  | .store a b => (.load (.mem b), .storeInd a, .load (.lit 0))
  | .add a b c => (.load (.mem b), .add (.mem c), .store a)
  | .sub a b c => (.load (.mem b), .sub (.mem c), .store a)
  | .mul a b c => (.load (.mem b), .mul (.mem c), .store a)
  | .div a b c => (.load (.mem b), .div (.mem c), .store a)
  | .and a b c => (.load (.mem b), .and (.mem c), .store a)
  | .not a b => (.load (.mem b), .compl (.lit 0), .store a)
  | .shiftl a b c => (.load (.mem b), .shiftl (.mem c), .store a)
  | .jump target => (.load (.lit 0), .load (.lit 0), .jump (3 * target))
  | .jzero a target => (.load (.mem a), .load (.mem a), .jzero (3 * target))
  | .halt => (.halt, .halt, .halt)
  | .read a => (.read a, .load (.lit 0), .load (.lit 0))
  | .write a => (.write (.mem a), .load (.lit 0), .load (.lit 0))

def block (i : Lax13.Ram.Instr) : Microcode.Program :=
  [(lower i).1, (lower i).2.1, (lower i).2.2]

def compile (p : Lax13.Ram.Program) : Microcode.Program := p.flatMap block

@[simp] theorem block_length (i : Lax13.Ram.Instr) : (block i).length = 3 := rfl

@[simp] theorem compile_length (p : Lax13.Ram.Program) :
    (compile p).length = 3 * p.length := by
  induction p with
  | nil => rfl
  | cons i p ih =>
      change (block i ++ compile p).length = _
      simp only [List.length_append, block_length, ih, List.length_cons, Nat.mul_succ]
      omega

theorem compile_get (p : Lax13.Ram.Program) (pc offset : Nat) (hoff : offset < 3) :
    (compile p)[3 * pc + offset]? = p[pc]?.bind (fun i => (block i)[offset]?) := by
  induction p generalizing pc with
  | nil => simp [compile]
  | cons i p ih =>
      cases pc with
      | zero => simp [compile, List.getElem?_append, hoff]
      | succ pc =>
          have hlarge : ¬3 * (pc + 1) + offset < 3 := by omega
          change (block i ++ compile p)[3 * (pc + 1) + offset]? = _
          simp only [List.getElem?_append, block_length, hlarge, if_false,
            List.getElem?_cons_succ]
          have heq : 3 * (pc + 1) + offset - 3 = 3 * pc + offset := by omega
          rw [heq]
          exact ih pc

def embed (s : Lax13.Ram.State) (accumulator : Nat) : Microcode.State :=
  { pc := 3 * s.pc, acc := accumulator, mem := s.mem, inp := s.inp, out := s.out }

def Normalized (w : Nat) (s : Lax13.Ram.State) : Prop :=
  ∀ a, s.mem a < 2 ^ w

theorem normalized_init (w : Nat) (input : List Nat) :
    Normalized w (Lax13.Ram.initState input) := by
  intro a
  exact Nat.two_pow_pos w

theorem normalized_effect {w : Nat} {s s' : Lax13.Ram.State}
    {i : Lax13.Ram.Instr} (hs : Normalized w s)
    (heffect : i.effect w s = some s') : Normalized w s' := by
  have hwrite (a v : Nat) : ∀ b, Lax13.Ram.setCell w s.mem a v b < 2 ^ w := by
    intro b
    simp only [Lax13.Ram.setCell]
    split
    · exact Nat.mod_lt _ (Nat.two_pow_pos w)
    · exact hs b
  cases i <;> simp [Lax13.Ram.Instr.effect] at heffect
  case read a =>
    cases hin : s.inp with
    | nil => simp [hin] at heffect
    | cons v vs =>
        simp [hin] at heffect
        subst s'
        exact hwrite a v
  all_goals
    subst s'
    first | exact hs | exact hwrite _ _

theorem effect_three {w : Nat} {p : Lax13.Ram.Program}
    {s s' : Lax13.Ram.State} {i : Lax13.Ram.Instr}
    (hfetch : p[s.pc]? = some i) (hs : Normalized w s)
    (heffect : i.effect w s = some s') (accumulator : Nat) :
    ∃ finalAccumulator,
      Microcode.run w (compile p) 3 (embed s accumulator) =
        some (embed s' finalAccumulator) := by
  have h0 : (compile p)[3 * s.pc]? = some (lower i).1 := by
    simpa [hfetch, block] using compile_get p s.pc 0 (by omega)
  have h1 : (compile p)[3 * s.pc + 1]? = some (lower i).2.1 := by
    simpa [hfetch, block] using compile_get p s.pc 1 (by omega)
  have h2 : (compile p)[3 * s.pc + 2]? = some (lower i).2.2 := by
    simpa [hfetch, block] using compile_get p s.pc 2 (by omega)
  have hmod (a : Nat) : s.mem a % 2 ^ w = s.mem a := Nat.mod_eq_of_lt (hs a)
  cases i <;> simp [Lax13.Ram.Instr.effect] at heffect
  case read a =>
    cases hin : s.inp with
    | nil => simp [hin] at heffect
    | cons v vs =>
        simp [hin] at heffect
        subst s'
        exact ⟨0, by
          simp [Microcode.run, Microcode.step, embed, h0, h1, h2,
            lower, Microcode.Instr.effect, Microcode.Op.value, hin,
            Nat.add_assoc, Nat.mul_add]
          rfl⟩
  all_goals
    subst s'
    simp [Microcode.run, Microcode.step, embed, h0, h1, h2,
      lower, Microcode.Instr.effect, Microcode.Op.value, hmod,
      Nat.add_assoc, Nat.mul_add,
      Microcode.State.mk.injEq] <;>
      (funext address; simp [Microcode.setCell, Lax13.Ram.setCell])

theorem microcode_run_add (w : Nat) (p : Microcode.Program) (m n : Nat)
    (s : Microcode.State) :
    Microcode.run w p (m + n) s =
      (Microcode.run w p m s).bind (Microcode.run w p n) := by
  induction m generalizing s with
  | zero => simp [Microcode.run]
  | succ m ih => simp [Nat.succ_add, Microcode.run, ih, Option.bind_assoc]

theorem run_translation {w t : Nat} {p : Lax13.Ram.Program}
    {s s' : Lax13.Ram.State} (hs : Normalized w s)
    (hrun : Lax13.Ram.run w p t s = some s') (accumulator : Nat) :
    ∃ finalAccumulator, Microcode.run w (compile p) (3 * t) (embed s accumulator) =
      some (embed s' finalAccumulator) := by
  induction t generalizing s accumulator with
  | zero =>
      simp [Lax13.Ram.run] at hrun
      subst s'
      exact ⟨accumulator, rfl⟩
  | succ t ih =>
      simp only [Lax13.Ram.run] at hrun
      cases hstep : Lax13.Ram.step w p s with
      | none => simp [hstep] at hrun
      | some middle =>
          simp only [hstep, Option.bind_some] at hrun
          cases hfetch : p[s.pc]? with
          | none => simp [Lax13.Ram.step, hfetch] at hstep
          | some i =>
              have heffect : i.effect w s = some middle := by
                simpa [Lax13.Ram.step, hfetch] using hstep
              obtain ⟨middleAccumulator, hthree⟩ := effect_three hfetch hs heffect accumulator
              obtain ⟨finalAccumulator, hrest⟩ := ih (normalized_effect hs heffect)
                hrun middleAccumulator
              refine ⟨finalAccumulator, ?_⟩
              rw [show 3 * (t + 1) = 3 + 3 * t by omega, microcode_run_add, hthree]
              exact hrest

theorem halt_translation {w : Nat} {p : Lax13.Ram.Program} {s : Lax13.Ram.State}
    (hhalt : Lax13.Ram.step w p s = none) (accumulator : Nat) :
    Microcode.step w (compile p) (embed s accumulator) = none := by
  have h0 := compile_get p s.pc 0 (by omega)
  cases hfetch : p[s.pc]? with
  | none =>
      have hfirst : (compile p)[3 * s.pc]? = none := by simpa [hfetch] using h0
      simp [Microcode.step, embed, hfirst]
  | some i =>
      have heffect : i.effect w s = none := by
        simpa [Lax13.Ram.step, hfetch] using hhalt
      have hfirst : (compile p)[3 * s.pc]? = some (lower i).1 := by
        simpa [hfetch, block] using h0
      cases i <;> simp [Lax13.Ram.Instr.effect] at heffect
      case halt => simp [Microcode.step, embed, hfirst, lower, Microcode.Instr.effect]
      case read a =>
        cases hin : s.inp with
        | nil => simp [Microcode.step, embed, hfirst, lower, Microcode.Instr.effect, hin]
        | cons v vs => simp [hin] at heffect

/-- Exact execution preservation, with the same width and exactly three
microcode steps per current RAM instruction. -/
theorem runsTo {w t : Nat} {p : Lax13.Ram.Program} {input output : List Nat}
    (hrun : Lax13.Ram.RunsTo w p input output t) :
    Microcode.RunsTo w (compile p) input output (3 * t) := by
  obtain ⟨s, hrun, hhalt, hout⟩ := hrun
  obtain ⟨accumulator, hmicro⟩ := run_translation (normalized_init w input) hrun 0
  exact ⟨embed s accumulator, hmicro, halt_translation hhalt accumulator, hout⟩

/-- Transfer the public polynomial-time hypothesis to the internal simulator.
Only the time polynomial changes, by a factor of three. -/
theorem polytime {f : List Nat → List Nat} (hf : Lax51.RamPolytime.RamPolytime f) :
    ∃ (p : Microcode.Program) (wordBound timeBound : Polynomial Nat),
      ∀ x, Lax51.RamPolytime.FitsInWords
          (wordBound.eval (Lax51.BinaryWordEncoding.bitSize x)) ((x.length :: x) ++ f x) ∧
        ∀ w, wordBound.eval (Lax51.BinaryWordEncoding.bitSize x) ≤ w →
          ∃ t ≤ timeBound.eval (Lax51.BinaryWordEncoding.bitSize x),
            Microcode.RunsTo w p (x.length :: x) (f x) t := by
  obtain ⟨p, wordBound, timeBound, hram⟩ := hf
  refine ⟨compile p, wordBound, 3 * timeBound, ?_⟩
  intro x
  obtain ⟨hfits, hall⟩ := hram x
  refine ⟨hfits, ?_⟩
  intro w hw
  obtain ⟨t, ht, hrun⟩ := hall w hw
  exact ⟨3 * t, by simpa using Nat.mul_le_mul_left 3 ht, runsTo hrun⟩

/-- The threshold function is retained, including its computability proof. -/
theorem computable {f : List Nat → List Nat}
    (hf : Lax51.TuringRamEquivalence.RamComputable f) :
    ∃ (p : Microcode.Program) (threshold : List Nat → Nat), Computable threshold ∧
      ∀ x w, threshold x ≤ w → ∃ t, Microcode.RunsTo w p (x.length :: x) (f x) t := by
  obtain ⟨p, threshold, hthreshold, hram⟩ := hf
  refine ⟨compile p, threshold, hthreshold, ?_⟩
  intro x w hw
  obtain ⟨t, ht⟩ := hram x w hw
  exact ⟨3 * t, runsTo ht⟩

end Lax51Proofs.CellToMicrocode
