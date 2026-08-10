import Lax51Proofs.RamToTM.InterpreterDispatcher

namespace Lax51Proofs.RamToTM

open Turing TM2 Lax13.Ram

noncomputable section

abbrev LocalCode (L : Type) [Fintype L] := Fin (Fintype.card L)

def localCodeEquiv (L : Type) [Fintype L] : L ≃ LocalCode L :=
  Fintype.equivFin _

set_option maxHeartbeats 2000000 in
inductive FiniteInterpreterLabel (p : Program) (N : Nat)
  | fetch (pc : BoundedPC p)
  | read (pc : BoundedPC p) (address : Fin (N + 1))
      (code : LocalCode
        (ReadInstructionLabel address.val (Sum (BoundedPC p) Unit)))
  | write (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (WriteInstructionLabel o.toOp (BoundedPC p)))
  | load (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (LoadInstructionLabel o.toOp (BoundedPC p)))
  | store (pc : BoundedPC p) (address : Fin (N + 1))
      (code : LocalCode (StoreInstructionLabel address.val (BoundedPC p)))
  | storeInd (pc : BoundedPC p) (address : Fin (N + 1))
      (code : LocalCode (StoreIndInstructionLabel address.val (BoundedPC p)))
  | add (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (AddInstructionLabel o.toOp (BoundedPC p)))
  | sub (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (SubtractInstructionLabel o.toOp (BoundedPC p)))
  | mul (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (MulInstructionLabel o.toOp (BoundedPC p)))
  | div (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (DivideInstructionTotalLabel o.toOp (BoundedPC p)))
  | bitwise (pc : BoundedPC p) (kind : BitwiseKind) (o : BoundedOp N)
      (code : LocalCode (ZipInstructionLabel o.toOp (BoundedPC p)))
  | shift (pc : BoundedPC p) (rightShift : Bool) (o : BoundedOp N)
      (code : LocalCode (ShiftInstructionLabel o.toOp (BoundedPC p)))
  | control (label : ControlDispatchLabel p)
  deriving Fintype, Inhabited

noncomputable instance (p : Program) (N : Nat) :
    DecidableEq (FiniteInterpreterLabel p N) := Classical.decEq _

abbrev FiniteRamLabel (p : Program) :=
  FiniteInterpreterLabel p (programArgumentBound p)

def encodeReadLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (address : Fin (N + 1))
    (label : ReadInstructionLabel address.val (Sum (BoundedPC p) Unit)) :
    FiniteInterpreterLabel p N :=
  match label with
  | .inr (.inr (.inr (.inr ()))) => .control .stopped
  | label => .read pc address (localCodeEquiv _ label)

def encodeWriteLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N) (label : WriteInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N :=
  .write pc o (localCodeEquiv _ label)

def encodeLoadLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N) (label : LoadInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N :=
  .load pc o (localCodeEquiv _ label)

def encodeStoreLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (address : Fin (N + 1))
    (label : StoreInstructionLabel address.val (BoundedPC p)) :
    FiniteInterpreterLabel p N :=
  .store pc address (localCodeEquiv _ label)

def encodeStoreIndLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (address : Fin (N + 1))
    (label : StoreIndInstructionLabel address.val (BoundedPC p)) :
    FiniteInterpreterLabel p N :=
  .storeInd pc address (localCodeEquiv _ label)

def encodeAddLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N) (label : AddInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .add pc o (localCodeEquiv _ label)

def encodeSubLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N) (label : SubtractInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .sub pc o (localCodeEquiv _ label)

def encodeMulLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N) (label : MulInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .mul pc o (localCodeEquiv _ label)

def encodeDivLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N)
    (label : DivideInstructionTotalLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .div pc o (localCodeEquiv _ label)

def encodeBitwiseLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (kind : BitwiseKind) (o : BoundedOp N)
    (label : ZipInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .bitwise pc kind o (localCodeEquiv _ label)

def encodeShiftLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (rightShift : Bool) (o : BoundedOp N)
    (label : ShiftInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .shift pc rightShift o (localCodeEquiv _ label)

def wrapFiniteLocal {p : Program} {N : Nat} {L : Type} [Fintype L]
    (encode : L -> FiniteInterpreterLabel p N) (next : BoundedPC p)
    (program : L -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)) (code : LocalCode L) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) :=
  let label := (localCodeEquiv L).symm code
  let stmt := program label
  if stmtIsHalt stmt then .goto fun _ => .fetch next
  else mapLabelStmt encode stmt

def finiteEmbedControlLabel {p : Program} {N : Nat} :
    ControlDispatchLabel p -> FiniteInterpreterLabel p N
  | .fetch pc => .fetch pc
  | .scanAccumulator pc target z => .control (.scanAccumulator pc target z)
  | .restoreAccumulator pc target z => .control (.restoreAccumulator pc target z)
  | .data pc kind => .control (.data pc kind)
  | .stopped => .control .stopped

def finiteControlStmt {p : Program} {N : Nat} (label : ControlDispatchLabel p) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) :=
  mapLabelStmt
    (fun
      | Sum.inl l => finiteEmbedControlLabel l
      | Sum.inr e => nomatch e)
    (lensRenameStmt (Λx := Empty) coreIdentityRenaming
      FullInterpreterState.dispatchLens ((controlDispatchMachine p).m label))

def finiteInitializeEntry {p : Program} {N : Nat} (n : Nat) (hn : n <= N)
    (entry : FiniteInterpreterLabel p N) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) :=
  .load (fun s => FullInterpreterState.literalLens.put s
    (BoundedLiteralControl.initial hn)) (.goto fun _ => entry)

def finitePrepareInstr (p : Program) (N : Nat)
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (i : Instr) (hfetch : pc.fetch = some i) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) := by
  have hi := instrArgument_le_of_boundedFetch pc hfetch
  have harg : instrArgument i <= N := hi.trans hbound
  cases i with
  | read a =>
          let address := boundedAddress a (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry a (by simpa [instrArgument] using harg)
            (encodeReadLabel pc address (operandEvalStartLabel (.lit a)))
  | write o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeWriteLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | load o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeLoadLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | store a =>
          let address := boundedAddress a (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry a (by simpa [instrArgument] using harg)
            (encodeStoreLabel pc address (operandEvalStartLabel (.lit a)))
  | storeInd a =>
          let address := boundedAddress a (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry a (by simpa [instrArgument] using harg)
            (encodeStoreIndLabel pc address (operandEvalStartLabel (.mem a)))
  | add o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeAddLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | sub o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeSubLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | mul o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeMulLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | div o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeDivLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | and o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeBitwiseLabel pc .and bo
              (by simpa [bo] using operandEvalStartLabel o))
  | or o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeBitwiseLabel pc .or bo
              (by simpa [bo] using operandEvalStartLabel o))
  | xor o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeBitwiseLabel pc .xor bo
              (by simpa [bo] using operandEvalStartLabel o))
  | shiftl o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeShiftLabel pc false bo
              (by simpa [bo] using operandEvalStartLabel o))
  | shiftr o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeShiftLabel pc true bo
              (by simpa [bo] using operandEvalStartLabel o))
  | jump _ | jzero _ | jgtz _ | halt => exact .halt

def finitePrepareEntry (p : Program) (N : Nat)
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) :=
  match hfetch : pc.fetch with
  | none => .halt
  | some i => finitePrepareInstr p N hbound pc i hfetch

theorem finitePrepareEntry_of_fetch {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (i : Instr) (hfetch : pc.fetch = some i) :
    finitePrepareEntry p N hbound pc =
      finitePrepareInstr p N hbound pc i hfetch := by
  unfold finitePrepareEntry
  split
  · simp_all
  · rename_i j hj
    have hij : j = i := Option.some.inj (hj.symm.trans hfetch)
    subst j
    rfl

def finiteInterpreterProgram (p : Program) (N : Nat)
    (hbound : programArgumentBound p <= N) :
    FiniteInterpreterLabel p N -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N)
  | .fetch pc => finiteControlStmt (.fetch pc)
  | .control (.data pc _) => finitePrepareEntry p N hbound pc
  | .control label => finiteControlStmt label
  | .read pc address code => wrapFiniteLocal (encodeReadLabel pc address)
      (nextPC p pc) (readInstructionProgram address.val (.inr ())
        (.inl (nextPC p pc)) (fun _ => .halt)) code
  | .write pc o code => wrapFiniteLocal (encodeWriteLabel pc o)
      (nextPC p pc) (writeInstructionProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .load pc o code => wrapFiniteLocal (encodeLoadLabel pc o)
      (nextPC p pc) (loadInstructionProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .store pc address code => wrapFiniteLocal (encodeStoreLabel pc address)
      (nextPC p pc) (storeInstructionProgram address.val (nextPC p pc) (fun _ => .halt)) code
  | .storeInd pc address code => wrapFiniteLocal (encodeStoreIndLabel pc address)
      (nextPC p pc) (storeIndInstructionProgram address.val (nextPC p pc) (fun _ => .halt)) code
  | .add pc o code => wrapFiniteLocal (encodeAddLabel pc o)
      (nextPC p pc) (addInstructionProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .sub pc o code => wrapFiniteLocal (encodeSubLabel pc o)
      (nextPC p pc) (subtractInstructionProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .mul pc o code => wrapFiniteLocal (encodeMulLabel pc o)
      (nextPC p pc) (mulInstructionProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .div pc o code => wrapFiniteLocal (encodeDivLabel pc o)
      (nextPC p pc) (divideInstructionTotalProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .bitwise pc kind o code => wrapFiniteLocal (encodeBitwiseLabel pc kind o)
      (nextPC p pc) (bitwiseInstructionProgram kind o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .shift pc rightShift o code => wrapFiniteLocal (encodeShiftLabel pc rightShift o)
      (nextPC p pc) (shiftInstructionProgram o.toOp rightShift (nextPC p pc) (fun _ => .halt)) code

noncomputable def finiteRamInterpreterMachine (p : Program) : Turing.FinTM2 where
  K := CoreStack
  k₀ := .input
  k₁ := .output
  Γ _ := SparseSymbol
  Λ := FiniteRamLabel p
  main := .fetch (boundPC p 0)
  σ := FullInterpreterState (programArgumentBound p)
  initialState := default
  m := finiteInterpreterProgram p (programArgumentBound p) le_rfl

def finiteInterpreterCfg {p : Program} {N : Nat}
    (label : FiniteInterpreterLabel p N) (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) := ⟨some label, state, tapes⟩

def finiteBoundaryCfg (p : Program) (pc w : Nat) (s : SparseState)
    (state : FullInterpreterState (programArgumentBound p)) :
    (finiteRamInterpreterMachine p).Cfg :=
  finiteInterpreterCfg (.fetch (boundPC p pc)) state (coreStacks w s)

def finiteEmbedCfg {p : Program} {N : Nat} {L : Type} [Fintype L]
    (encode : L -> FiniteInterpreterLabel p N)
    (c : TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) := mapLabelCfg encode c

theorem wrapFiniteLocal_encode_nonhalt {p : Program} {N : Nat} {L : Type}
    [Fintype L] (encode : L -> FiniteInterpreterLabel p N)
    (next : BoundedPC p)
    (program : L -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)) (label : L) (h : program label ≠ .halt) :
    wrapFiniteLocal encode next program (localCodeEquiv L label) =
      mapLabelStmt encode (program label) := by
  simp [wrapFiniteLocal, stmtIsHalt_eq_true_iff, h]

theorem transport_finiteLocal_run {p : Program} {N n : Nat} {L : Type}
    [Fintype L] (encode : L -> FiniteInterpreterLabel p N)
    (next : BoundedPC p)
    (program : L -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (target : FiniteInterpreterLabel p N -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N))
    (htarget : ∀ label, target (encode label) =
      wrapFiniteLocal encode next program (localCodeEquiv L label))
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)}
    (hrun : ((fun x => x.bind (TM2.step program))^[n]) (some c) = some d)
    (hd : d.l.isSome) :
    ((fun x => x.bind (TM2.step target))^[n])
      (some (finiteEmbedCfg encode c)) = some (finiteEmbedCfg encode d) := by
  apply iterate_mapLabelProgram_until_exit program target encode
  · intro label hn
    rw [htarget]
    exact wrapFiniteLocal_encode_nonhalt encode next program label hn
  · exact hrun
  · exact hd

theorem finite_step_local_exit {p : Program} {N : Nat} {L : Type}
    [Fintype L] (encode : L -> FiniteInterpreterLabel p N)
    (next : BoundedPC p)
    (program : L -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (target : FiniteInterpreterLabel p N -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N))
    (htarget : ∀ label, target (encode label) =
      wrapFiniteLocal encode next program (localCodeEquiv L label))
    (label : L) (h : program label = .halt)
    (state : FullInterpreterState N) (tapes : CoreStack -> List SparseSymbol) :
    TM2.step target (finiteInterpreterCfg (encode label) state tapes) =
      some (finiteInterpreterCfg (.fetch next) state tapes) := by
  change some (TM2.stepAux (target (encode label)) state tapes) = _
  rw [htarget]
  simp [wrapFiniteLocal, h, stmtIsHalt, finiteInterpreterCfg, TM2.step]

theorem transport_finiteLocal_run_to_fetch
    {p : Program} {N n : Nat} {L : Type} [Fintype L]
    (encode : L -> FiniteInterpreterLabel p N) (next : BoundedPC p)
    (program : L -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (target : FiniteInterpreterLabel p N -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N))
    (htarget : ∀ label, target (encode label) =
      wrapFiniteLocal encode next program (localCodeEquiv L label))
    {c : TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)}
    (finalLabel : L) (finalState : FullInterpreterState N)
    (finalTapes : CoreStack -> List SparseSymbol)
    (hrun : ((fun x => x.bind (TM2.step program))^[n]) (some c) =
      some (⟨some finalLabel, finalState, finalTapes⟩ :
        TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
          (FullInterpreterState N)))
    (hhalt : program finalLabel = .halt) :
    ((fun x => x.bind (TM2.step target))^[n + 1])
      (some (finiteEmbedCfg encode c)) =
      some (finiteInterpreterCfg (.fetch next) finalState finalTapes) := by
  have htransport := transport_finiteLocal_run encode next program target
    htarget hrun (by rfl)
  have hexit := finite_step_local_exit encode next program target htarget
    finalLabel hhalt finalState finalTapes
  have htransport' :
      ((fun x => x.bind (TM2.step target))^[n])
        (some (finiteEmbedCfg encode c)) =
      some (finiteInterpreterCfg (encode finalLabel) finalState finalTapes) := by
    simpa [finiteEmbedCfg, mapLabelCfg, finiteInterpreterCfg] using htransport
  have hexit' :
      ((fun x => x.bind (TM2.step target))^[1])
        (some (finiteInterpreterCfg (encode finalLabel) finalState finalTapes)) =
      some (finiteInterpreterCfg (.fetch next) finalState finalTapes) := by
    simpa using hexit
  exact chain_iterations
    (fun x : Option (TM2.Cfg (fun _ : CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step target))
    htransport' hexit'

theorem cfg_eq_some_get {α K L σ : Type}
    (c : TM2.Cfg (fun _ : K => α) L σ) (h : c.l.isSome) :
    c = ⟨some (c.l.get h), c.var, c.stk⟩ := by
  cases c with
  | mk label state tapes =>
      cases label <;> simp_all

theorem transport_finiteLocal_cfg_to_fetch
    {p : Program} {N n : Nat} {L : Type} [Fintype L]
    (encode : L -> FiniteInterpreterLabel p N) (next : BoundedPC p)
    (program : L -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (target : FiniteInterpreterLabel p N -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N))
    (htarget : ∀ label, target (encode label) =
      wrapFiniteLocal encode next program (localCodeEquiv L label))
    {c d : TM2.Cfg (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)}
    (hrun : ((fun x => x.bind (TM2.step program))^[n]) (some c) = some d)
    (hd : d.l.isSome) (hhalt : program (d.l.get hd) = .halt) :
    ((fun x => x.bind (TM2.step target))^[n + 1])
      (some (finiteEmbedCfg encode c)) =
      some (finiteInterpreterCfg (.fetch next) d.var d.stk) := by
  rw [cfg_eq_some_get d hd] at hrun
  exact transport_finiteLocal_run_to_fetch encode next program target htarget
    (d.l.get hd) d.var d.stk hrun hhalt

theorem finite_step_fetch_data {p : Program} {N pc : Nat}
    (hbound : programArgumentBound p <= N) {i : Instr}
    (hfetch : p[pc]? = some i) (hdata : i ≠ .halt)
    (hnjump : match i with
      | .jump _ | .jzero _ | .jgtz _ => False
      | _ => True)
    (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol) :
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes) =
    some (finiteInterpreterCfg
      (.control (.data (boundPC p pc) (instrClass i))) state tapes) := by
  have hpc : pc < p.length := fetch_some_pc_lt hfetch
  have hget : p[pc] = i := by
    simpa [List.getElem?_eq_getElem hpc] using hfetch
  cases i <;>
    simp_all [finiteInterpreterProgram, finiteControlStmt,
      finiteInterpreterCfg, controlDispatchMachine, fetch_boundPC,
      mapLabelStmt, lensRenameStmt, coreIdentityRenaming,
      FullInterpreterState.dispatchLens, FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens, StateLens.comp, TM2.step,
      renamedStacks, finiteEmbedControlLabel, hget]
  all_goals contradiction

theorem finite_step_load_entry {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p) (o : Op)
    (hfetch : pc.fetch = some (.load o))
    (state : FullInterpreterState N) (tapes : CoreStack -> List SparseSymbol) :
    let harg : operandArgument o <= N :=
      (instrArgument_le_of_boundedFetch pc hfetch).trans hbound
    let bo := BoundedOp.ofOp o harg
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data pc .load)) state tapes) =
    some (finiteInterpreterCfg
      (encodeLoadLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
      (FullInterpreterState.literalLens.put state
        (BoundedLiteralControl.initial harg)) tapes) := by
  dsimp only
  change some (TM2.stepAux (finitePrepareEntry p N hbound pc) state tapes) = _
  rw [finitePrepareEntry_of_fetch hbound pc (.load o) hfetch]
  simp [finitePrepareInstr,
    finiteInitializeEntry, instrArgument, finiteInterpreterCfg, TM2.stepAux]

theorem finite_step_prepare_entry {p : Program} {N : Nat}
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (i : Instr) (kind : InstrClass) (hfetch : pc.fetch = some i)
    (hclass : instrClass i = kind)
    (state : FullInterpreterState N) (tapes : CoreStack -> List SparseSymbol) :
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data pc kind)) state tapes) =
    some (TM2.stepAux (finitePrepareInstr p N hbound pc i hfetch)
      state tapes) := by
  subst kind
  change some (TM2.stepAux (finitePrepareEntry p N hbound pc) state tapes) = _
  rw [finitePrepareEntry_of_fetch hbound pc i hfetch]

end

end Lax51Proofs.RamToTM
