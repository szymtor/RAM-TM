import Lax759944Proofs.Legacy.RamComputes
import Lax808846.RamComputes

/-!
Checked embedding of the legacy sequential-input RAM into the RAM with
immutable indexed input and a separate output tape. This bridge lets existing
compiler implementations remain proof-internal while their generated programs
execute on `Lax808846.Ram`.

Every legacy instruction retains its meaning and program counter. The original
input is carried unchanged in the additional state field. The supplied list is
unchanged: this embedding adds no framing and performs no initial input scan.

The legacy `RunsTo` counts successful transitions. The current model also
charges an explicit `halt` or an exhausted `read`, so the current execution
cost is the legacy cost or one more. This distinction includes empty programs,
which still cost zero. No word-length or address-space enlargement is needed.
-/

namespace Lax759944Proofs.LegacyRamBridge

/-- Preserve each legacy instruction in the extended instruction set. -/
def embedInstr : Lax759944Proofs.Legacy.Ram.Instr → Lax808846.Ram.Instr
  | .set a n => .set a n
  | .load a b => .load a b
  | .store a b => .store a b
  | .add a b c => .add a b c
  | .sub a b c => .sub a b c
  | .mul a b c => .mul a b c
  | .div a b c => .div a b c
  | .and a b c => .and a b c
  | .shiftl a b c => .shiftl a b c
  | .not a b => .not a b
  | .jump l => .jump l
  | .jzero a l => .jzero a l
  | .halt => .halt
  | .read a => .read a
  | .write a => .write a

/-- Embed a program without changing instruction positions. -/
def embedProgram (p : Lax759944Proofs.Legacy.Ram.Program) : Lax808846.Ram.Program :=
  p.map embedInstr

/-- Add the immutable original input to a legacy state. -/
def embedState (input : List ℕ) (s : Lax759944Proofs.Legacy.Ram.State) :
    Lax808846.Ram.State where
  pc := s.pc
  mem := s.mem
  input := input
  inp := s.inp
  out := s.out

@[simp] theorem embedProgram_length (p : Lax759944Proofs.Legacy.Ram.Program) :
    (embedProgram p).length = p.length := by
  simp [embedProgram]

@[simp] theorem embed_initState (input : List ℕ) :
    embedState input (Lax759944Proofs.Legacy.Ram.initState input) =
      Lax808846.Ram.initState input := rfl

/-- One instruction preserves the state embedding, including input storage. -/
theorem effect_embed (w : ℕ) (i : Lax759944Proofs.Legacy.Ram.Instr)
    (input : List ℕ) (s : Lax759944Proofs.Legacy.Ram.State) :
    (embedInstr i).effect w (embedState input s) =
      (i.effect w s).map (embedState input) := by
  cases i <;> try rfl
  case read a =>
    cases hinp : s.inp <;>
      simp [embedInstr, embedState, Lax759944Proofs.Legacy.Ram.Instr.effect,
        Lax808846.Ram.Instr.effect, hinp]
    rfl

/-- Instruction fetch commutes with the embedding at every program counter. -/
theorem step_embed (w : ℕ) (p : Lax759944Proofs.Legacy.Ram.Program)
    (input : List ℕ) (s : Lax759944Proofs.Legacy.Ram.State) :
    Lax808846.Ram.step w (embedProgram p) (embedState input s) =
      (Lax759944Proofs.Legacy.Ram.step w p s).map (embedState input) := by
  simp only [Lax808846.Ram.step, embedProgram, embedState,
    List.getElem?_map, Lax759944Proofs.Legacy.Ram.step]
  cases hfetch : p[s.pc]? with
  | none => rfl
  | some i => exact effect_embed w i input s

/-- Successful transitions are preserved exactly at the same word length. -/
theorem run_embed (w : ℕ) (p : Lax759944Proofs.Legacy.Ram.Program)
    (t : ℕ) (input : List ℕ) (s : Lax759944Proofs.Legacy.Ram.State) :
    Lax808846.Ram.run w (embedProgram p) t (embedState input s) =
      (Lax759944Proofs.Legacy.Ram.run w p t s).map (embedState input) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      simp only [Lax808846.Ram.run, Lax759944Proofs.Legacy.Ram.run, step_embed]
      cases hstep : Lax759944Proofs.Legacy.Ram.step w p s with
      | none => rfl
      | some s' => exact ih s'

/-- A legacy computation incurs at most one additional terminal instruction. -/
theorem runsTo {w t : ℕ} {p : Lax759944Proofs.Legacy.Ram.Program}
    {input output : List ℕ}
    (h : Lax759944Proofs.Legacy.Ram.RunsTo w p input output t) :
    ∃ u, t ≤ u ∧ u ≤ t + 1 ∧
      Lax808846.Ram.RunsTo w (embedProgram p) input output u := by
  obtain ⟨s, hrun, hhalt, hout⟩ := h
  let cost := Lax808846.Ram.terminalCost (embedProgram p) (embedState input s)
  have hcost : cost ≤ 1 := by
    simp only [cost, Lax808846.Ram.terminalCost]
    split <;> omega
  refine ⟨t + cost, by omega, by omega, t, embedState input s, ?_, ?_, hout, rfl⟩
  · simpa [hrun] using run_embed w p t input (Lax759944Proofs.Legacy.Ram.initState input)
  · simpa [hhalt] using step_embed w p input s

/-- Transfer a time bound to the current RAM, including its terminal cost. -/
theorem computesInTime {w : ℕ} {p : Lax759944Proofs.Legacy.Ram.Program}
    {D : Set (List ℕ)} {f : List ℕ → List ℕ} {T : List ℕ → ℕ}
    (h : Lax759944Proofs.Legacy.RamComputes.ComputesInTime w p D f T) :
    Lax808846.RamComputes.ComputesInTime w (embedProgram p) D f
      (fun input => T input + 1) := by
  intro input hinput
  obtain ⟨t, ht, hrun⟩ := h input hinput
  obtain ⟨u, _, hu, hnew⟩ := runsTo hrun
  exact ⟨u, by change u ≤ T input + 1; omega, hnew⟩

end Lax759944Proofs.LegacyRamBridge
