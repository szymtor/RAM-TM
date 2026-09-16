import Lax759944Proofs.Computability.SparseRamBasic
import Lax759944.TuringRamEquivalence

/-!
A finite sparse evaluator for the current RAM. The immutable original input
and the remaining sequential tape are separate fields. Every instruction,
including EOF detection and indexed input, is simulated without changing word
length or data-memory addressing. This evaluator is used for computability;
no complexity bound for its implementation is asserted here.
-/

namespace Lax759944Proofs.Computability.TapeRam

open Lax808846.Ram
open Lax759944Proofs.RamToTM (SparseMemory)

structure Config where
  pc : ℕ
  mem : SparseMemory
  input : List ℕ
  inp : List ℕ
  out : List ℕ

def Config.toState (s : Config) : State :=
  ⟨s.pc, s.mem.read, s.input, s.inp, s.out⟩

def initial (x : List ℕ) : Config := ⟨0, [], x, x, []⟩

@[simp] theorem initial_toState (x : List ℕ) :
    (initial x).toState = initState x := rfl

def effect (w : ℕ) : Instr → Config → Option Config
  | .set a n, s => some { s with pc := s.pc + 1, mem := s.mem.write w a n }
  | .load a b, s => some { s with pc := s.pc + 1, mem := s.mem.write w a (s.mem.read (s.mem.read (b % 2 ^ w) % 2 ^ w)) }
  | .store a b, s => some { s with pc := s.pc + 1, mem := s.mem.write w (s.mem.read (a % 2 ^ w)) (s.mem.read (b % 2 ^ w)) }
  | .add a b c, s => some { s with pc := s.pc + 1, mem := s.mem.write w a (s.mem.read (b % 2 ^ w) + s.mem.read (c % 2 ^ w)) }
  | .sub a b c, s => some { s with pc := s.pc + 1, mem := s.mem.write w a (s.mem.read (b % 2 ^ w) - s.mem.read (c % 2 ^ w)) }
  | .mul a b c, s => some { s with pc := s.pc + 1, mem := s.mem.write w a (s.mem.read (b % 2 ^ w) * s.mem.read (c % 2 ^ w)) }
  | .div a b c, s => some { s with pc := s.pc + 1, mem := s.mem.write w a (s.mem.read (b % 2 ^ w) / s.mem.read (c % 2 ^ w)) }
  | .and a b c, s => some { s with pc := s.pc + 1, mem := s.mem.write w a (Nat.land (s.mem.read (b % 2 ^ w)) (s.mem.read (c % 2 ^ w))) }
  | .shiftl a b c, s => some { s with pc := s.pc + 1, mem := s.mem.write w a (s.mem.read (b % 2 ^ w) * 2 ^ s.mem.read (c % 2 ^ w)) }
  | .not a b, s => some { s with pc := s.pc + 1, mem := s.mem.write w a (2 ^ w - 1 - s.mem.read (b % 2 ^ w)) }
  | .jump l, s => some { s with pc := l }
  | .jzero a l, s =>
      some { s with pc := if s.mem.read (a % 2 ^ w) = 0 then l else s.pc + 1 }
  | .jeof l, s => some { s with pc := if s.inp.isEmpty then l else s.pc + 1 }
  | .inputLength a, s =>
      some { s with pc := s.pc + 1, mem := s.mem.write w a s.input.length }
  | .inputLoad a b, s => some { s with pc := s.pc + 1, mem := s.mem.write w a (s.input[s.mem.read (b % 2 ^ w) % 2 ^ w]?.getD 0) }
  | .halt, _ => none
  | .read a, s => s.inp.head?.map fun v =>
      { s with pc := s.pc + 1, mem := s.mem.write w a v, inp := s.inp.tail }
  | .write a, s => some { s with pc := s.pc + 1, out := s.out ++ [s.mem.read (a % 2 ^ w) % 2 ^ w] }

private theorem write_toState (w : ℕ) (m : SparseMemory) (a v : ℕ) :
    (m.write w a v).read = setCell w m.read a v := by
  funext b
  rfl

/-- Every instruction has exactly the public RAM effect. -/
theorem effect_toState (w : ℕ) (i : Instr) (s : Config) :
    (effect w i s).map Config.toState = i.effect w s.toState := by
  cases i <;> simp [effect, Config.toState, Instr.effect, write_toState]
  case jzero => rfl
  case read a =>
    cases s.inp <;> simp [Config.toState, write_toState]

def next (w : ℕ) (p : Program) (s : Config) : Option Config :=
  p[s.pc]?.bind fun i => effect w i s

theorem next_toState (w : ℕ) (p : Program) (s : Config) :
    (next w p s).map Config.toState = step w p s.toState := by
  simp only [next, step, Config.toState]
  cases hfetch : p[s.pc]? with
  | none => rfl
  | some i => exact effect_toState w i s

def execute (w : ℕ) (p : Program) : ℕ → Config → Option Config
  | 0, s => some s
  | t + 1, s => (next w p s).bind (execute w p t)

theorem execute_toState (w : ℕ) (p : Program) (t : ℕ) (s : Config) :
    (execute w p t s).map Config.toState = run w p t s.toState := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      rw [execute, run, ← next_toState]
      cases hn : next w p s with
      | none => rfl
      | some s' => exact ih s'

/-- Any public finite execution has a finite sparse representative. -/
theorem execute_exists {w t : ℕ} {p : Program} {x : List ℕ} {s : State}
    (h : run w p t (initState x) = some s) :
    ∃ c, execute w p t (initial x) = some c ∧ c.toState = s := by
  have heq := execute_toState w p t (initial x)
  rw [initial_toState, h] at heq
  cases hc : execute w p t (initial x) with
  | none => simp [hc] at heq
  | some c =>
      simp [hc] at heq
      exact ⟨c, rfl, heq⟩

/-- Return output only after a halting configuration has been reached. -/
def haltOutput (p : Program) (w : ℕ) (s : Config) : Option (List ℕ) :=
  match next w p s with
  | none => some s.out
  | some _ => none

def candidateAt (p : Program) (w : ℕ) (x : List ℕ) (t : ℕ) : Option (List ℕ) :=
  (execute w p t (initial (x.length :: x))).bind (haltOutput p w)

theorem candidate_exists_of_runsTo {p : Program} {w t : ℕ} {x y : List ℕ}
    (h : RunsTo w p (x.length :: x) y t) :
    ∃ k, candidateAt p w x k = some y := by
  obtain ⟨k, s, hrun, hhalt, hout, _⟩ := h
  obtain ⟨c, hc, hcs⟩ := execute_exists hrun
  have hn : next w p c = none := by
    have heq := next_toState w p c
    rw [hcs, hhalt] at heq
    exact Option.map_eq_none_iff.mp heq
  have ho : c.out = y := by
    have h := congrArg State.out hcs
    exact h.trans hout
  exact ⟨k, by simp [candidateAt, hc, haltOutput, hn, ho]⟩

theorem runsTo_of_candidate {p : Program} {w k : ℕ} {x y : List ℕ}
    (h : candidateAt p w x k = some y) :
    ∃ t, RunsTo w p (x.length :: x) y t := by
  unfold candidateAt at h
  cases hc : execute w p k (initial (x.length :: x)) with
  | none => simp [hc] at h
  | some c =>
      simp only [hc, Option.bind_some] at h
      unfold haltOutput at h
      cases hn : next w p c with
      | some c' => simp [hn] at h
      | none =>
          simp [hn] at h
          refine ⟨k + terminalCost p c.toState, k, c.toState, ?_, ?_, ?_, rfl⟩
          · simpa [hc] using (execute_toState w p k (initial (x.length :: x))).symm
          · simpa [hn] using (next_toState w p c).symm
          · exact h

private theorem run_add (w : ℕ) (p : Program) (m n : ℕ) (s : State) :
    run w p (m + n) s = (run w p m s).bind (run w p n) := by
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih => simp [Nat.succ_add, run, ih, Option.bind_assoc]

private theorem run_positive_of_halt {w : ℕ} {p : Program} {s : State}
    (hhalt : step w p s = none) {t : ℕ} (ht : 0 < t) : run w p t s = none := by
  cases t with
  | zero => omega
  | succ t => simp [run, hhalt]

/-- Determinism identifies the complete output of any two halting runs. -/
theorem runsTo_output_unique {w : ℕ} {p : Program} {x y z : List ℕ}
    {t u : ℕ} (hy : RunsTo w p x y t) (hz : RunsTo w p x z u) : y = z := by
  obtain ⟨k, sy, hry, hhy, hoy, _⟩ := hy
  obtain ⟨l, sz, hrz, hhz, hoz, _⟩ := hz
  have hkl : k = l := by
    rcases lt_trichotomy k l with hlt | heq | hgt
    · rw [show l = k + (l - k) by omega, run_add, hry] at hrz
      simp only [Option.bind_some] at hrz
      rw [run_positive_of_halt hhy (by omega)] at hrz
      contradiction
    · exact heq
    · rw [show k = l + (k - l) by omega, run_add, hrz] at hry
      simp only [Option.bind_some] at hry
      rw [run_positive_of_halt hhz (by omega)] at hry
      contradiction
  subst l
  have hs : sy = sz := by simpa [hry] using hrz
  subst sz
  exact hoy.symm.trans hoz

end Lax759944Proofs.Computability.TapeRam
