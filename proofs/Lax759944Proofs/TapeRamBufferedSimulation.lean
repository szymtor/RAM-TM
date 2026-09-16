import Lax759944Proofs.TapeRamBufferedRead
import Lax759944Proofs.TapeRamBufferedIndexed
import Lax759944Proofs.TapeRamBufferedPrelude

namespace Lax759944Proofs.TapeRamBufferedSimulation

open Lax808846.Ram TapeRamVirtualMemory TapeRamVirtualMacros
open TapeRamBufferedCompiler TapeRamBufferedState

/-- Input snapshots are immutable under every source instruction. -/
theorem effect_input {v : Nat} {instruction : Instr} {source next : State}
    (heffect : instruction.effect v source = some next) : next.input = source.input := by
  cases instruction <;> simp only [Instr.effect] at heffect
  all_goals try { cases heffect; rfl }
  case halt => cases heffect
  case read address =>
    cases hinput : source.inp with
    | nil => simp [hinput] at heffect
    | cons value rest => simp [hinput] at heffect; cases heffect; rfl

def withoutCursor (source : State) : State := { source with inp := [] }

theorem core_effect_withoutCursor {v : Nat} {instruction : Instr} {source next : State}
    (hcore : CoreInstruction instruction)
    (heffect : instruction.effect v source = some next) :
    instruction.effect v (withoutCursor source) = some (withoutCursor next) := by
  cases instruction <;> simp only [CoreInstruction] at hcore
  all_goals try contradiction
  all_goals simp only [Instr.effect] at heffect ⊢
  all_goals try { cases heffect; rfl }
  all_goals contradiction

theorem core_run_paddedBody {v extra : Nat} {values : List Nat} {program : Program}
    {instruction : Instr} {source next : State} {scratch : Nat → Nat} {cursor : Nat}
    (hcapacity : 16 ≤ 2 ^ (v + 1)) (hfetch : program[source.pc]? = some instruction)
    (hcore : CoreInstruction instruction) (hinput : source.input = values)
    (hscratch : AdapterScratch v values cursor scratch)
    (hnormal : Normalized v source.mem)
    (heffect : instruction.effect v source = some next) :
    ∃ nextScratch,
      AdapterScratch v values cursor nextScratch ∧ BranchReady v instruction source nextScratch ∧
      run (v + 1) (compile extra program) 16
        (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16) next.mem nextScratch [] next.out) := by
  have hnextInput := (effect_input heffect).trans hinput
  have heffect' := core_effect_withoutCursor hcore heffect
  rcases TapeRamVirtualSimulation.paddedBody_effect (physicalPc := location source.pc)
      (source := withoutCursor source) (next := withoutCursor next) hcapacity hscratch.compiler hnormal heffect' with
    ⟨nextScratch, hcompiler, hready, hhigh, hbody⟩
  refine ⟨nextScratch, hscratch.preserve hcompiler hhigh, ?_, ?_⟩
  · cases instruction <;> simp only [CoreInstruction] at hcore
    all_goals try contradiction
    all_goals simpa only [BranchReady, TapeRamVirtualSimulation.BranchReady, withoutCursor] using hready
  · have hlinear : ∀ i ∈ TapeRamVirtualCompiler.paddedBody instruction, StraightLine i := by
      intro i hi
      simp only [TapeRamVirtualCompiler.paddedBody, List.mem_append, List.mem_replicate] at hi
      rcases hi with hi | ⟨_, rfl⟩
      · exact body_straightLine instruction i hi
      · trivial
    have hprefix : ∀ k, k < (TapeRamVirtualCompiler.paddedBody instruction).length →
        (compile extra program)[(state values (location source.pc) source.mem scratch [] source.out).pc + k]? =
          (TapeRamVirtualCompiler.paddedBody instruction)[k]? := by
      intro k hk
      rw [← paddedBody_eq_of_core program.length source.pc instruction hcore]
      exact compile_get_paddedBody extra program source.pc instruction hfetch k (by simpa using hk)
    rw [show 16 = (TapeRamVirtualCompiler.paddedBody instruction).length by simp,
      run_eq_execute _ _ _ _ hlinear hprefix]
    simpa only [withoutCursor, hinput, hnextInput, TapeRamVirtualCompiler.paddedBody_length] using hbody

theorem run_branch {v extra : Nat} {values remaining : List Nat} {program : Program} {i : Instr}
    {source next : State} {scratch : Nat → Nat}
    (hcapacity : 16 ≤ 2 ^ (v + 1)) (hfetch : program[source.pc]? = some i)
    (hready : BranchReady v i source scratch)
    (heffect : i.effect v source = some next) :
    ∃ cost, 1 ≤ cost ∧ cost ≤ 2 ∧
      run (v + 1) (compile extra program) cost
        (state values (location source.pc + 16) next.mem scratch remaining next.out) =
        some (state values (location next.pc) next.mem scratch remaining next.out) := by
  have hfirst := compile_get_branch extra program source.pc i hfetch 0 (by omega)
  have hsecond := compile_get_branch extra program source.pc i hfetch 1 (by omega)
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
        simp [run, step, hfirst, branch, Instr.effect, state, h11, htest, hzero,
          TapeRamVirtualCompiler.resultRegister]
      · refine ⟨2, by omega, by omega, ?_⟩
        simp [run, step, hfirst, hsecond, branch, Instr.effect, state, h11,
          htest, hzero, TapeRamVirtualCompiler.resultRegister]
  | jeof target =>
      simp only [Instr.effect] at heffect
      cases heffect
      simp only [BranchReady] at hready
      have htest : merge source.mem scratch 11 = scratch 5 := by
        exact merge_odd source.mem scratch 5
      by_cases hempty : source.inp = []
      · have hzero := hready.mpr hempty
        refine ⟨1, by omega, by omega, ?_⟩
        simp [run, step, hfirst, branch, Instr.effect, state,
          TapeRamVirtualCompiler.resultRegister, h11, htest, hzero, hempty]
      · have hzero : scratch 5 ≠ 0 := fun h => hempty (hready.mp h)
        refine ⟨2, by omega, by omega, ?_⟩
        simp [run, step, hfirst, hsecond, branch, Instr.effect, state,
          TapeRamVirtualCompiler.resultRegister, h11, htest, hzero, hempty]
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


theorem core_effect_inp {v : Nat} {instruction : Instr} {source next : State}
    (hcore : CoreInstruction instruction)
    (heffect : instruction.effect v source = some next) : next.inp = source.inp := by
  cases instruction <;> simp only [CoreInstruction] at hcore
  all_goals try contradiction
  all_goals simp only [Instr.effect] at heffect
  all_goals try { cases heffect; rfl }
  all_goals contradiction

/-- Finish a translated source step after its body has reached branch slot 16. -/
theorem finish_step {v extra bodyCost cursor : Nat} {values : List Nat} {program : Program}
    {instruction : Instr} {source next : State} {scratch nextScratch : Nat → Nat}
    (hcapacity : 16 ≤ 2 ^ (v + 1)) (hfetch : program[source.pc]? = some instruction)
    (heffect : instruction.effect v source = some next)
    (hnormal : Normalized v source.mem) (hinput : next.input = values)
    (hseq : next.inp = values.drop cursor) (hadapter : AdapterScratch v values cursor nextScratch)
    (hready : BranchReady v instruction source nextScratch) (hcost : bodyCost ≤ 16)
    (hbody : run (v + 1) (compile extra program) bodyCost
      (state values (location source.pc) source.mem scratch [] source.out) =
        some (state values (location source.pc + 16) next.mem nextScratch [] next.out)) :
    ∃ cost nextPhysical,
      cost ≤ 18 ∧
      run (v + 1) (compile extra program) cost
        (state values (location source.pc) source.mem scratch [] source.out) = some nextPhysical ∧
      Simulates v values next nextPhysical := by
  rcases run_branch (extra := extra) (values := values) (remaining := []) hcapacity hfetch hready heffect with
    ⟨branchCost, _, hbranchCost, hbranch⟩
  let nextPhysical := state values (location next.pc) next.mem nextScratch [] next.out
  refine ⟨bodyCost + branchCost, nextPhysical, by omega, ?_, ?_⟩
  · rw [run_add, hbody, Option.bind_some, hbranch]
  · exact ⟨cursor, nextScratch, hinput, hseq,
      TapeRamVirtualSimulation.normalized_effect hnormal heffect, hadapter, rfl⟩

/-- Every source instruction has an at-most-eighteen-step buffered simulation. -/
theorem simulation_step {v extra : Nat} {values : List Nat} {program : Program}
    {source next physical : State}
    (hcapacity : values.length + 32 < 2 ^ v)
    (hfit : ∀ value ∈ values, value < 2 ^ v)
    (hsimulates : Simulates v values source physical)
    (hstep : step v program source = some next) :
    ∃ cost nextPhysical,
      cost ≤ 18 ∧ run (v + 1) (compile extra program) cost physical = some nextPhysical ∧
      Simulates v values next nextPhysical := by
  rcases hsimulates with ⟨cursor, scratch, hinput, hseq, hnormal, hadapter, rfl⟩
  have hlarge := TapeRamBufferedInputs.large_capacity hcapacity
  simp only [step] at hstep
  cases hfetch : program[source.pc]? with
  | none => simp [hfetch] at hstep
  | some instruction =>
      rw [hfetch] at hstep
      simp only [Option.bind_some] at hstep
      have hnextInput := (effect_input hstep).trans hinput
      by_cases hcore : CoreInstruction instruction
      · rcases core_run_paddedBody (extra := extra) (by omega) hfetch hcore hinput hadapter
          hnormal hstep with ⟨nextScratch, hnextAdapter, hready, hbody⟩
        exact finish_step (by omega) hfetch hstep hnormal hnextInput
          ((core_effect_inp hcore hstep).trans hseq) hnextAdapter hready (by omega) hbody
      · cases instruction <;> simp only [CoreInstruction] at hcore
        all_goals try contradiction
        case read address =>
          have hnonempty : source.inp ≠ [] := by
            intro hnil
            simp [Instr.effect, hnil] at hstep
          have hcursor : cursor < values.length := by
            by_contra h
            exact hnonempty (hseq.trans (List.drop_eq_nil_iff.mpr (by omega)))
          have hsourceSeq := hseq.trans (List.drop_eq_getElem_cons hcursor)
          have hsaved := hstep
          simp only [Instr.effect, hsourceSeq, List.head?_cons, Option.map_some, List.tail_cons] at hstep
          cases hstep
          rcases TapeRamBufferedRead.read_run (extra := extra) (memory := source.mem)
              (output := source.out) hcapacity hfit hfetch hadapter hcursor with
            ⟨nextScratch, hnextAdapter, hbody⟩
          exact finish_step (by omega) hfetch hsaved hnormal hnextInput rfl
            hnextAdapter (by trivial) (by omega) hbody
        case inputLength address =>
          have hsaved := hstep
          simp only [Instr.effect] at hstep
          cases hstep
          rcases TapeRamBufferedInputs.inputLength_run (extra := extra)
              hcapacity hfetch hadapter with ⟨nextScratch, hnextAdapter, hbody⟩
          apply finish_step (bodyCost := 16) (by omega) hfetch hsaved hnormal hnextInput hseq
            hnextAdapter (by trivial) (by omega)
          simpa only [hinput] using hbody
        case inputLoad address index =>
          have hsaved := hstep
          simp only [Instr.effect] at hstep
          cases hstep
          rcases TapeRamBufferedIndexed.inputLoad_run (extra := extra)
              hcapacity hfetch hnormal hadapter with
            ⟨bodyCost, hbodyCost, nextScratch, hnextAdapter, hbody⟩
          apply finish_step (by omega) hfetch hsaved hnormal hnextInput hseq
            hnextAdapter (by trivial) hbodyCost
          simpa only [hinput, Nat.mod_eq_of_lt (hnormal _)] using hbody
        case jeof target =>
          have hsaved := hstep
          simp only [Instr.effect] at hstep
          cases hstep
          rcases TapeRamBufferedInputs.jeof_run (extra := extra)
              hcapacity hfetch hseq hadapter with ⟨nextScratch, hnextAdapter, hready, hbody⟩
          exact finish_step (by omega) hfetch hsaved hnormal hnextInput hseq
            hnextAdapter hready (by omega) hbody

/-- Compose any finite run without weakening the source instruction set. -/
theorem simulation_run {v extra time : Nat} {values : List Nat} {program : Program}
    {source next physical : State} (hcapacity : values.length + 32 < 2 ^ v)
    (hfit : ∀ value ∈ values, value < 2 ^ v)
    (hsimulates : Simulates v values source physical)
    (hrun : run v program time source = some next) :
    ∃ cost nextPhysical,
      cost ≤ 18 * time ∧ run (v + 1) (compile extra program) cost physical = some nextPhysical ∧
      Simulates v values next nextPhysical := by
  induction time generalizing source next physical with
  | zero =>
      simp only [run] at hrun
      cases hrun
      exact ⟨0, physical, by omega, by simp [run], hsimulates⟩
  | succ time ih =>
      simp only [run] at hrun
      cases hfirst : step v program source with
      | none => simp [hfirst] at hrun
      | some middle =>
          rw [hfirst] at hrun
          simp only [Option.bind_some] at hrun
          rcases simulation_step (extra := extra) hcapacity hfit hsimulates hfirst with
            ⟨firstCost, middlePhysical, hfirstCost, hfirstRun, hmiddle⟩
          rcases ih hmiddle hrun with ⟨restCost, nextPhysical, hrestCost, hrestRun, hnext⟩
          refine ⟨firstCost + restCost, nextPhysical, by omega, ?_, hnext⟩
          rw [run_add, hfirstRun, Option.bind_some, hrestRun]

/-- Termination is matched after at most sixteen successful preparation steps. -/
theorem simulation_halt {v extra : Nat} {values : List Nat} {program : Program}
    {source physical : State} (hcapacity : values.length + 32 < 2 ^ v)
    (hsimulates : Simulates v values source physical)
    (hhalt : step v program source = none) :
    ∃ cost final,
      cost ≤ 16 ∧ run (v + 1) (compile extra program) cost physical = some final ∧
      step (v + 1) (compile extra program) final = none ∧ final.out = source.out := by
  rcases hsimulates with ⟨cursor, scratch, hinput, hseq, hnormal, hadapter, rfl⟩
  have hlarge := TapeRamBufferedInputs.large_capacity hcapacity
  simp only [step] at hhalt
  cases hfetch : program[source.pc]? with
  | none =>
      have hpc : program.length ≤ source.pc := List.getElem?_eq_none_iff.mp hfetch
      refine ⟨0, state values (location source.pc) source.mem scratch [] source.out,
        by omega, by simp [run], ?_, rfl⟩
      by_cases hequal : source.pc = program.length
      · simp only [step, state, hequal, compile_get_halt, Option.bind_some, Instr.effect]
      · have houtside := compile_get_outside extra program source.pc (by omega)
        simp only [step, state, houtside, Option.bind_none]
  | some instruction =>
      rw [hfetch] at hhalt
      simp only [Option.bind_some] at hhalt
      cases instruction with
      | halt =>
          let padding : Program := List.replicate 16 (.set 5 0)
          have hpaddingDef : paddedBody program.length source.pc Instr.halt = padding := rfl
          have hlinear : ∀ i ∈ padding, StraightLine i := by
            simp [padding, StraightLine]
          have hprefix : ∀ k, k < padding.length →
              (compile extra program)[location source.pc + k]? = padding[k]? := by
            intro k hk
            rw [← hpaddingDef]
            exact compile_get_paddedBody extra program source.pc Instr.halt hfetch k
              (by simpa [padding] using hk)
          rcases padding_execute (original := values) v 16 (location source.pc) source.mem scratch
              [] source.out (by omega) hadapter.compiler with
            ⟨nextScratch, _, _, _, hpadding⟩
          let final := state values (location source.pc + 16) source.mem nextScratch [] source.out
          have hrun : run (v + 1) (compile extra program) 16
              (state values (location source.pc) source.mem scratch [] source.out) = some final := by
            rw [show 16 = padding.length by simp [padding],
              run_eq_execute _ _ _ _ hlinear hprefix]
            exact hpadding
          have hbranch := compile_get_branch extra program source.pc Instr.halt hfetch 0 (by omega)
          simp only [Nat.add_zero, branch, List.getElem?_cons_zero] at hbranch
          refine ⟨16, final, by omega, hrun, ?_, rfl⟩
          simp only [step, final, state, hbranch, Option.bind_some, Instr.effect]
      | read address =>
          cases hremaining : source.inp with
          | nil =>
              have hcursor : cursor = values.length := by
                have hle := List.drop_eq_nil_iff.mp (hseq.symm.trans hremaining)
                have := hadapter.cursor_le
                omega
              subst cursor
              rcases TapeRamBufferedRead.read_exhausted (extra := extra) (memory := source.mem)
                  (output := source.out) hcapacity hfetch hadapter with
                ⟨final, hrun, hterminal, houtput⟩
              exact ⟨2, final, by omega, hrun, hterminal, houtput⟩
          | cons value rest => simp [Instr.effect, hremaining] at hhalt
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

/-- Snapshot framed input once, then simulate every instruction of the full
Lax808846 machine using only the legacy instructions in the emitted program. -/
theorem runsTo_compile {v extra header time : Nat} {program : Program}
    {tail output : List Nat}
    (hlength : (header :: tail).length = header + extra)
    (hfit : ∀ value ∈ header :: tail, value < 2 ^ v)
    (hcapacity : (header :: tail).length + 32 < 2 ^ v)
    (hrun : RunsTo v program (header :: tail) output time) :
    ∃ physicalTime ≤ 18 * time + 6 * (header :: tail).length + 26,
      RunsTo (v + 1) (compile extra program) (header :: tail) output physicalTime := by
  rcases hrun with ⟨sourceSteps, sourceFinal, hsourceRun, hsourceHalt, houtput, htime⟩
  rcases TapeRamBufferedPrelude.compile_start v extra header tail program hcapacity hlength hfit with
    ⟨scratch, hadapter, hstart⟩
  let start := state (header :: tail) (location 0) (fun _ => 0) scratch [] []
  have hsimulates : Simulates v (header :: tail) (initState (header :: tail)) start := by
    refine ⟨0, scratch, rfl, by simp [initState], ?_, hadapter, rfl⟩
    exact TapeRamVirtualSimulation.normalized_init v (header :: tail)
  rcases simulation_run (extra := extra) hcapacity hfit hsimulates hsourceRun with
    ⟨runCost, runFinal, hrunCost, hsimulatedRun, hfinalSimulates⟩
  rcases simulation_halt (extra := extra) hcapacity hfinalSimulates hsourceHalt with
    ⟨haltCost, final, hhaltCost, hhaltRun, hterminal, hfinalOutput⟩
  have hterminalCost : terminalCost (compile extra program) final ≤ 1 := by
    unfold terminalCost
    split <;> omega
  let steps := 6 * (header :: tail).length + 9 + runCost + haltCost
  refine ⟨steps + terminalCost (compile extra program) final, by dsimp [steps]; omega,
    steps, final, ?_, hterminal, hfinalOutput.trans houtput, rfl⟩
  change run (v + 1) (compile extra program)
    (6 * (header :: tail).length + 9 + runCost + haltCost)
    (initState (header :: tail)) = some final
  rw [show 6 * (header :: tail).length + 9 + runCost + haltCost =
      (6 * (header :: tail).length + 9) + (runCost + haltCost) by omega,
    run_add, hstart, Option.bind_some, run_add, hsimulatedRun, Option.bind_some, hhaltRun]

end Lax759944Proofs.TapeRamBufferedSimulation
