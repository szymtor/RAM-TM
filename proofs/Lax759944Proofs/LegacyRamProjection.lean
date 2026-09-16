import Lax759944Proofs.LegacyRamBridge

/-!
Projection of executions using only the historical instruction set.
The restriction applies to a compiler's generated code, never to a public
computability predicate. It is intended for input-buffer compilers that
implement indexed input and EOF with ordinary memory operations.
-/

namespace Lax759944Proofs.LegacyRamProjection

open LegacyRamBridge

/-- Exactly the instructions represented by the internal sequential machine. -/
def IsLegacy : Lax808846.Ram.Instr → Prop
  | .jeof _ | .inputLength _ | .inputLoad _ _ => False
  | _ => True

/-- Project instruction syntax. Unsupported cases are never used under
`IsLegacy`; they are mapped to halt to keep this function total. -/
def eraseInstr : Lax808846.Ram.Instr → Legacy.Ram.Instr
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
  | .jeof _ | .inputLength _ | .inputLoad _ _ => .halt

def eraseProgram (p : Lax808846.Ram.Program) : Legacy.Ram.Program :=
  p.map eraseInstr

theorem embed_erase_instr {i : Lax808846.Ram.Instr} (hi : IsLegacy i) :
    embedInstr (eraseInstr i) = i := by
  cases i <;> simp_all [IsLegacy, eraseInstr, embedInstr]

theorem embed_erase_program {p : Lax808846.Ram.Program}
    (hp : ∀ i ∈ p, IsLegacy i) : embedProgram (eraseProgram p) = p := by
  simp only [embedProgram, eraseProgram, List.map_map]
  calc
    p.map (embedInstr ∘ eraseInstr) = p.map id :=
      List.map_congr_left (fun i hi => embed_erase_instr (hp i hi))
    _ = p := List.map_id p

/-- An execution of an embedded program projects to a legacy execution.
Only the optional final terminal charge is removed. -/
theorem runsTo_embed {w t : ℕ} {p : Legacy.Ram.Program}
    {input output : List ℕ}
    (h : Lax808846.Ram.RunsTo w (embedProgram p) input output t) :
    ∃ k ≤ t, Legacy.Ram.RunsTo w p input output k := by
  obtain ⟨k, s, hr, hh, ho, ht⟩ := h
  have hr' := run_embed w p k input (Legacy.Ram.initState input)
  rw [embed_initState] at hr'
  cases he : Legacy.Ram.run w p k (Legacy.Ram.initState input) with
  | none => simp [he, hr] at hr'
  | some q =>
      have hs : embedState input q = s := by
        simpa [he, hr] using hr'.symm
      subst s
      refine ⟨k, by omega, q, he, ?_, ho⟩
      have hh' := step_embed w p input q
      rw [hh] at hh'
      cases hs : Legacy.Ram.step w p q with
      | none => rfl
      | some q' => simp [hs] at hh'

/-- The full new machine may execute the generated code; the compiler's
syntactic invariant suffices to recover a checked legacy execution. -/
theorem runsTo_erase {w t : ℕ} {p : Lax808846.Ram.Program}
    {input output : List ℕ} (hp : ∀ i ∈ p, IsLegacy i)
    (h : Lax808846.Ram.RunsTo w p input output t) :
    ∃ k ≤ t, Legacy.Ram.RunsTo w (eraseProgram p) input output k := by
  apply runsTo_embed
  simpa [embed_erase_program hp] using h

end Lax759944Proofs.LegacyRamProjection
