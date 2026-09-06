import Lax51Proofs.RamToTM.ProgramBound
import Lax51Proofs.RamToTM.LoadInstruction
import Lax51Proofs.RamToTM.AddInstruction
import Lax51Proofs.RamToTM.ZipInstruction
import Lax51Proofs.RamToTM.MultiplyInstruction
import Lax51Proofs.RamToTM.WriteInstruction
import Lax51Proofs.RamToTM.StoreIndInstruction
import Lax51Proofs.RamToTM.SubtractInstruction
import Lax51Proofs.RamToTM.DivideInstructionTotal

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax51Proofs.Microcode

noncomputable section

/-- The local phase type selected by the instruction at a program counter.
The type is finite for every counter because `p` itself is fixed. -/
def instructionLabelType (p : Program) (pc : BoundedPC p) : Type :=
  match pc.fetch with
  | some (.read a) => ReadInstructionLabel a (BoundedPC p)
  | some (.write o) => WriteInstructionLabel o (BoundedPC p)
  | some (.load o) => LoadInstructionLabel o (BoundedPC p)
  | some (.store a) => StoreInstructionLabel a (BoundedPC p)
  | some (.storeInd a) => StoreIndInstructionLabel a (BoundedPC p)
  | some (.add o) => AddInstructionLabel o (BoundedPC p)
  | some (.sub o) => SubtractInstructionLabel o (BoundedPC p)
  | some (.mul o) => MulInstructionLabel o (BoundedPC p)
  | some (.div o) => DivideInstructionTotalLabel o (BoundedPC p)
  | some (.and o) | some (.or o) | some (.xor o) | some (.compl o) =>
      ZipInstructionLabel o (BoundedPC p)
  | some (.shiftl o) | some (.shiftr o) =>
      ShiftInstructionLabel o (BoundedPC p)
  | _ => PUnit

noncomputable instance instructionLabelTypeFintype (p : Program)
    (pc : BoundedPC p) : Fintype (instructionLabelType p pc) := by
  unfold instructionLabelType
  split <;> infer_instance

/-- Finite control for the complete interpreter. Local dependent phase labels
are represented by their canonical finite indices. -/
inductive InterpreterLabel (p : Program) (N : Nat)
  | fetch (pc : BoundedPC p)
  | data (pc : BoundedPC p)
      (code : Fin (Fintype.card (instructionLabelType p pc)))
  | control (label : ControlDispatchLabel p)
  deriving Fintype, Inhabited

noncomputable instance (p : Program) (N : Nat) :
    DecidableEq (InterpreterLabel p N) := Classical.decEq _

noncomputable instance (p : Program) (N : Nat) :
    Fintype (InterpreterLabel p N) := Fintype.ofFinite _

abbrev RamInterpreterLabel (p : Program) :=
  InterpreterLabel p (programArgumentBound p)

def boundedAddress {N : Nat} (a : Nat) (h : a <= N) : Fin (N + 1) :=
  ⟨a, Nat.lt_succ_of_le h⟩

theorem instrArgument_le_of_boundedFetch {p : Program} (pc : BoundedPC p)
    {i : Instr} (hfetch : pc.fetch = some i) :
    instrArgument i <= programArgumentBound p := by
  have hlt : pc.val < p.length := by
    by_contra h
    simp [BoundedPC.fetch, h] at hfetch
  have hp : p[pc.val]? = some i := by
    simpa [BoundedPC.fetch, hlt] using hfetch
  exact instrArgument_le_programArgumentBound hp

def instructionNext (p : Program) (pc : BoundedPC p) : BoundedPC p :=
  nextPC p pc

def instructionEntry (p : Program) (pc : BoundedPC p) :
    Option (instructionLabelType p pc) := by
  unfold instructionLabelType
  split
  next h => exact some (operandEvalStartLabel (.lit _))
  next h => exact some (operandEvalStartLabel _)
  next h => exact some (operandEvalStartLabel _)
  next h => exact some (operandEvalStartLabel (.lit _))
  next h => exact some (operandEvalStartLabel (.mem _))
  next h => exact some (operandEvalStartLabel _)
  next h => exact some (operandEvalStartLabel _)
  next h => exact some (operandEvalStartLabel _)
  next h => exact some (operandEvalStartLabel _)
  next h => exact some (operandEvalStartLabel _)
  next h => exact some (operandEvalStartLabel _)
  next h => exact some (operandEvalStartLabel _)
  next h => exact some (operandEvalStartLabel _)
  next h => exact some (operandEvalStartLabel _)
  next h => exact some (operandEvalStartLabel _)
  all_goals exact none

def localLabelEquiv (p : Program) (pc : BoundedPC p) :
    instructionLabelType p pc ≃
      Fin (Fintype.card (instructionLabelType p pc)) :=
  Fintype.equivFin _

def embedInstructionLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (label : instructionLabelType p pc) : InterpreterLabel p N :=
  .data pc (localLabelEquiv p pc label)

def decodeInstructionLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (code : Fin (Fintype.card (instructionLabelType p pc))) :
    instructionLabelType p pc :=
  (localLabelEquiv p pc).symm code

@[simp] theorem decodeInstructionLabel_embed {p : Program} {N : Nat}
    (pc : BoundedPC p) (label : instructionLabelType p pc) :
    decodeInstructionLabel (N := N) pc (localLabelEquiv p pc label) = label := by
  simp [decodeInstructionLabel]

def stmtIsHalt {α K Λ σ : Type} : TM2.Stmt (fun _ : K => α) Λ σ -> Bool
  | .halt => true
  | _ => false

theorem stmtIsHalt_eq_true_iff {α K Λ σ : Type}
    (stmt : TM2.Stmt (fun _ : K => α) Λ σ) :
    stmtIsHalt stmt = true ↔ stmt = .halt := by
  cases stmt <;> simp [stmtIsHalt]

def localInstructionProgram (p : Program) (N : Nat) (pc : BoundedPC p) :
    instructionLabelType p pc -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (instructionLabelType p pc)
      (FullInterpreterState N) := by
  unfold instructionLabelType
  split
  next a h => exact (readInstructionProgram a (nextPC p pc) (nextPC p pc)
    (fun _ => .halt))
  next o h => exact writeInstructionProgram o (nextPC p pc) (fun _ => .halt)
  next o h => exact loadInstructionProgram o (nextPC p pc) (fun _ => .halt)
  next a h => exact storeInstructionProgram a (nextPC p pc) (fun _ => .halt)
  next a h => exact storeIndInstructionProgram a (nextPC p pc) (fun _ => .halt)
  next o h => exact addInstructionProgram o (nextPC p pc) (fun _ => .halt)
  next o h => exact subtractInstructionProgram o (nextPC p pc) (fun _ => .halt)
  next o h => exact mulInstructionProgram o (nextPC p pc) (fun _ => .halt)
  next o h => exact divideInstructionTotalProgram o (nextPC p pc) (fun _ => .halt)
  next o h => exact bitwiseInstructionProgram .and o (nextPC p pc) (fun _ => .halt)
  next o h => exact bitwiseInstructionProgram .or o (nextPC p pc) (fun _ => .halt)
  next o h => exact bitwiseInstructionProgram .xor o (nextPC p pc) (fun _ => .halt)
  next o h => exact bitwiseInstructionProgram .compl o (nextPC p pc) (fun _ => .halt)
  next o h => exact shiftInstructionProgram o false (nextPC p pc) (fun _ => .halt)
  next o h => exact shiftInstructionProgram o true (nextPC p pc) (fun _ => .halt)
  all_goals exact fun _ => .halt

def embedControlLabel {p : Program} {N : Nat} :
    ControlDispatchLabel p -> InterpreterLabel p N
  | .fetch pc => .fetch pc
  | .scanAccumulator pc target z => .control (.scanAccumulator pc target z)
  | .restoreAccumulator pc target z => .control (.restoreAccumulator pc target z)
  | .data pc kind => .control (.data pc kind)
  | .stopped => .control .stopped

def embeddedControlStmt {p : Program} {N : Nat} (label : ControlDispatchLabel p) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (InterpreterLabel p N)
      (FullInterpreterState N) :=
  mapLabelStmt
    (fun
      | Sum.inl l => embedControlLabel l
      | Sum.inr e => nomatch e)
    (lensRenameStmt (Λx := Empty) coreIdentityRenaming
      FullInterpreterState.dispatchLens ((controlDispatchMachine p).m label))

def prepareOperandEntry {p : Program} {N : Nat} (pc : BoundedPC p)
    (control : BoundedLiteralControl N) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (InterpreterLabel p N)
      (FullInterpreterState N) :=
  match instructionEntry p pc with
  | some entry =>
      .load (fun s => FullInterpreterState.literalLens.put s control) <|
        .goto fun _ => embedInstructionLabel pc entry
  | none => .halt

def prepareInstructionEntry (p : Program) (N : Nat)
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (InterpreterLabel p N)
      (FullInterpreterState N) := by
  cases hfetch : pc.fetch with
  | none => exact .halt
  | some i =>
      have hi := instrArgument_le_of_boundedFetch pc hfetch
      have harg : instrArgument i <= N := hi.trans hbound
      cases i with
      | read a | store a | storeInd a =>
          exact prepareOperandEntry pc
            (BoundedLiteralControl.initial
              (by simpa [instrArgument] using harg))
      | write o | load o | add o | sub o | mul o | div o
      | and o | or o | xor o | compl o | shiftl o | shiftr o =>
          exact prepareOperandEntry pc
            (BoundedLiteralControl.initial
              (by simpa [instrArgument] using harg))
      | jump _ | jzero _ | jgtz _ | halt => exact .halt

def interpreterProgram (p : Program) (N : Nat)
    (hbound : programArgumentBound p <= N) :
    InterpreterLabel p N -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (InterpreterLabel p N)
      (FullInterpreterState N)
  | .fetch pc => embeddedControlStmt (.fetch pc)
  | .control (.data pc _) => prepareInstructionEntry p N hbound pc
  | .control label => embeddedControlStmt label
  | .data pc code =>
      let label := decodeInstructionLabel (N := N) pc code
      let stmt := localInstructionProgram p N pc label
      if stmtIsHalt stmt then .goto fun _ => .fetch (nextPC p pc)
      else mapLabelStmt (embedInstructionLabel pc) stmt

noncomputable def ramInterpreterMachine (p : Program) : Turing.FinTM2 where
  K := CoreStack
  k₀ := .input
  k₁ := .output
  Γ _ := SparseSymbol
  Λ := RamInterpreterLabel p
  main := .fetch (boundPC p 0)
  σ := FullInterpreterState (programArgumentBound p)
  initialState := default
  m := interpreterProgram p (programArgumentBound p) le_rfl

def interpreterCfg {p : Program} {N : Nat} (label : InterpreterLabel p N)
    (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) (InterpreterLabel p N)
      (FullInterpreterState N) :=
  ⟨some label, state, tapes⟩

def interpreterBoundaryCfg (p : Program) (pc w : Nat) (s : SparseState)
    (state : FullInterpreterState (programArgumentBound p)) :
    (ramInterpreterMachine p).Cfg :=
  interpreterCfg (.fetch (boundPC p pc)) state (coreStacks w s)

def embedInstructionCfg {p : Program} {N : Nat} (pc : BoundedPC p)
    (c : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (instructionLabelType p pc) (FullInterpreterState N)) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) (InterpreterLabel p N)
      (FullInterpreterState N) :=
  mapLabelCfg (embedInstructionLabel pc) c

theorem interpreterProgram_data_nonhalt {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N)
    (pc : BoundedPC p) (label : instructionLabelType p pc)
    (h : localInstructionProgram p N pc label ≠ .halt) :
    interpreterProgram p N hbound (embedInstructionLabel pc label) =
      mapLabelStmt (embedInstructionLabel pc)
        (localInstructionProgram p N pc label) := by
  simp [interpreterProgram, embedInstructionLabel,
    decodeInstructionLabel, stmtIsHalt_eq_true_iff, h]

theorem transport_localInstruction_run {p : Program} {N n : Nat}
    (hbound : programArgumentBound p <= N)
    (pc : BoundedPC p)
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (instructionLabelType p pc) (FullInterpreterState N)}
    (hrun : ((fun x => x.bind
      (TM2.step (localInstructionProgram p N pc)))^[n]) (some c) = some d)
    (hd : d.l.isSome) :
    ((fun x => x.bind (TM2.step (interpreterProgram p N hbound)))^[n])
      (some (embedInstructionCfg pc c)) =
      some (embedInstructionCfg pc d) := by
  exact iterate_mapLabelProgram_until_exit
    (localInstructionProgram p N pc) (interpreterProgram p N hbound)
    (embedInstructionLabel pc) (interpreterProgram_data_nonhalt hbound pc)
    hrun hd

theorem interpreter_step_local_exit {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N)
    (pc : BoundedPC p) (label : instructionLabelType p pc)
    (h : localInstructionProgram p N pc label = .halt)
    (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol) :
    TM2.step (interpreterProgram p N hbound)
      (interpreterCfg (embedInstructionLabel pc label) state tapes) =
    some (interpreterCfg (.fetch (nextPC p pc)) state tapes) := by
  simp [interpreterProgram, interpreterCfg, embedInstructionLabel,
    decodeInstructionLabel, h, stmtIsHalt]

theorem interpreter_step_fetch_data {p : Program} {N pc : Nat}
    (hbound : programArgumentBound p <= N) {i : Instr}
    (hfetch : p[pc]? = some i)
    (hdata : i ≠ .halt)
    (hnjump : (match i with
      | .jump _ | .jzero _ | .jgtz _ => False
      | _ => True))
    (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol) :
    TM2.step (interpreterProgram p N hbound)
      (interpreterCfg (.fetch (boundPC p pc)) state tapes) =
    some (interpreterCfg
      (.control (.data (boundPC p pc) (instrClass i))) state tapes) := by
  have hpc : pc < p.length := fetch_some_pc_lt hfetch
  have hget : p[pc] = i := by
    simpa [List.getElem?_eq_getElem hpc] using hfetch
  cases i <;>
    simp_all [interpreterProgram, embeddedControlStmt, interpreterCfg,
      controlDispatchMachine, fetch_boundPC, mapLabelStmt, lensRenameStmt,
      lensRenameStmt, coreIdentityRenaming, FullInterpreterState.dispatchLens,
      FullInterpreterState.macroLens, InterpreterMacroState.dispatchLens,
      StateLens.comp, TM2.step, renamedStacks, embedControlLabel, hget]
  all_goals contradiction

theorem interpreter_step_control_data {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (kind : InstrClass) (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol) :
    TM2.step (interpreterProgram p N hbound)
      (interpreterCfg (.control (.data pc kind)) state tapes) =
    TM2.stepAux (prepareInstructionEntry p N hbound pc) state tapes := by
  rfl

theorem prepareOperandEntry_step {p : Program} {N : Nat}
    (pc : BoundedPC p) (control : BoundedLiteralControl N)
    (entry : instructionLabelType p pc)
    (hentry : instructionEntry p pc = some entry)
    (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol) :
    TM2.stepAux (prepareOperandEntry pc control) state tapes =
      interpreterCfg (embedInstructionLabel pc entry)
        (FullInterpreterState.literalLens.put state control) tapes := by
  simp [prepareOperandEntry, hentry, interpreterCfg, TM2.stepAux]

end

end Lax51Proofs.RamToTM
