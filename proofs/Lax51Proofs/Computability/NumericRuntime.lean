import Lax51Proofs.TMToRam.NumericMachine
import Mathlib.Computability.Primrec.List

namespace Lax51Proofs.Computability

open Turing Lax51Proofs.TMToRam

set_option maxHeartbeats 2000000

/-! A computable, finite representation of the numeric TM interpreter state. -/

abbrev SparseStackData := List (ℕ × List ℕ)

/-- A finite association list represents the finitely many nonempty numeric
stacks.  New bindings shadow old ones. -/
def sparseStackLookup (data : SparseStackData) (k : ℕ) : List ℕ :=
  (data.lookup k).getD []

def sparseStackUpdate (data : SparseStackData) (k : ℕ) (xs : List ℕ) :
    SparseStackData :=
  (k, xs) :: data

@[simp] theorem sparseStackLookup_update_same (data : SparseStackData)
    (k : ℕ) (xs : List ℕ) :
    sparseStackLookup (sparseStackUpdate data k xs) k = xs := by
  simp [sparseStackLookup, sparseStackUpdate, List.lookup]

@[simp] theorem sparseStackLookup_update_of_ne (data : SparseStackData)
    {k j : ℕ} (h : j ≠ k) (xs : List ℕ) :
    sparseStackLookup (sparseStackUpdate data k xs) j =
      sparseStackLookup data j := by
  have hb : (j == k) = false := beq_eq_false_iff_ne.mpr h
  simp [sparseStackLookup, sparseStackUpdate, List.lookup, hb]

theorem sparseStackLookup_update (data : SparseStackData) (k : ℕ)
    (xs : List ℕ) :
    (fun j => sparseStackLookup (sparseStackUpdate data k xs) j) =
      Function.update (fun j => sparseStackLookup data j) k xs := by
  funext j
  by_cases h : j = k
  · subst j
    simp
  · simp [h, Function.update_of_ne]

structure SparseNumericState where
  label : Option ℕ
  state : ℕ
  stackData : SparseStackData

abbrev SparseNumericStateData := (Option ℕ × ℕ) × SparseStackData

def sparseNumericStateEquiv : SparseNumericState ≃ SparseNumericStateData where
  toFun c := ((c.label, c.state), c.stackData)
  invFun d := { label := d.1.1, state := d.1.2, stackData := d.2 }
  left_inv c := by cases c; rfl
  right_inv d := by rcases d with ⟨⟨label, state⟩, stackEntries⟩; rfl

instance sparseNumericStatePrimcodable : Primcodable SparseNumericState :=
  Primcodable.ofEquiv SparseNumericStateData sparseNumericStateEquiv

theorem sparseNumericStateEquiv_primrec : Primrec sparseNumericStateEquiv :=
  Primrec.of_equiv

theorem sparseNumericStateEquiv_symm_primrec :
    Primrec sparseNumericStateEquiv.symm :=
  Primrec.of_equiv_symm

theorem sparseNumericState_label_primrec : Primrec SparseNumericState.label :=
  (Primrec.fst.comp (Primrec.fst.comp sparseNumericStateEquiv_primrec)).of_eq
    fun _ => rfl

theorem sparseNumericState_state_primrec : Primrec SparseNumericState.state :=
  (Primrec.snd.comp (Primrec.fst.comp sparseNumericStateEquiv_primrec)).of_eq
    fun _ => rfl

theorem sparseNumericState_stackData_primrec :
    Primrec SparseNumericState.stackData :=
  (Primrec.snd.comp sparseNumericStateEquiv_primrec).of_eq fun _ => rfl

theorem sparseNumericState_mk_primrec {α : Type*} [Primcodable α]
    {label : α → Option ℕ} {state : α → ℕ}
    {stackData : α → SparseStackData}
    (hlabel : Primrec label) (hstate : Primrec state)
    (hstacks : Primrec stackData) :
    Primrec fun a =>
      ({ label := label a, state := state a,
         stackData := stackData a } : SparseNumericState) := by
  exact sparseNumericStateEquiv_symm_primrec.comp
    (Primrec.pair (Primrec.pair hlabel hstate) hstacks)

theorem sparseStackLookup_primrec₂ : Primrec₂ sparseStackLookup := by
  change Primrec fun q : SparseStackData × ℕ =>
    ((q.1.lookup q.2).getD ([] : List ℕ))
  exact Primrec.option_getD.comp
    (Primrec.listLookup.comp Primrec.snd Primrec.fst)
    (Primrec.const [])

theorem sparseStackUpdate_primrec :
    Primrec fun q : SparseStackData × (ℕ × List ℕ) =>
      sparseStackUpdate q.1 q.2.1 q.2.2 := by
  exact Primrec.list_cons.comp
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))
    Primrec.fst

def SparseNumericState.toNumeric (c : SparseNumericState) :
    NumericMachineState where
  label := c.label
  state := c.state
  stackData := sparseStackLookup c.stackData

def execSparse : NumericStmt → SparseNumericState → SparseNumericState
  | .push k table next, c =>
      let xs := table.getD c.state 0 :: sparseStackLookup c.stackData k
      execSparse next { c with stackData := sparseStackUpdate c.stackData k xs }
  | .peek k width table next, c =>
      let i := c.state * width + headCode (sparseStackLookup c.stackData k)
      execSparse next { c with state := table.getD i 0 }
  | .pop k width table next, c =>
      let stack := sparseStackLookup c.stackData k
      let i := c.state * width + headCode stack
      let stackEntries := sparseStackUpdate c.stackData k stack.tail
      execSparse next { c with state := table.getD i 0, stackData := stackEntries }
  | .load table next, c => execSparse next { c with state := table.getD c.state 0 }
  | .branch table yes no, c =>
      if table.getD c.state 0 = 0 then execSparse no c else execSparse yes c
  | .goto table, c => { c with label := some (table.getD c.state 0) }
  | .halt, c => { c with label := none }

theorem execSparse_toNumeric (q : NumericStmt)
    (c : SparseNumericState) :
    (execSparse q c).toNumeric = q.exec c.toNumeric := by
  induction q generalizing c with
  | push k table next ih =>
      simp only [execSparse, NumericStmt.exec]
      rw [ih]
      apply congrArg (NumericStmt.exec next)
      apply NumericMachineState.ext
      · rfl
      · rfl
      · exact sparseStackLookup_update _ _ _
  | peek k width table next ih =>
      simp only [execSparse, NumericStmt.exec]
      exact ih _
  | pop k width table next ih =>
      simp only [execSparse, NumericStmt.exec]
      rw [ih]
      apply congrArg (NumericStmt.exec next)
      apply NumericMachineState.ext
      · rfl
      · rfl
      · exact sparseStackLookup_update _ _ _
  | load table next ih =>
      simp only [execSparse, NumericStmt.exec]
      exact ih _
  | branch table yes no ihYes ihNo =>
      by_cases h : table.getD c.state 0 = 0
      · simp only [execSparse, NumericStmt.exec, if_pos h]
        have h' : table.getD c.toNumeric.state 0 = 0 := by
          simpa [SparseNumericState.toNumeric] using h
        rw [if_pos h']
        exact ihNo c
      · simp only [execSparse, NumericStmt.exec, if_neg h]
        have h' : ¬table.getD c.toNumeric.state 0 = 0 := by
          simpa [SparseNumericState.toNumeric] using h
        rw [if_neg h']
        exact ihYes c
  | goto table => rfl
  | halt => rfl

theorem headCode_primrec : Primrec headCode := by
  exact (Primrec.list_casesOn (f := fun xs : List ℕ => xs)
    (g := fun _ => 0) (h := fun _ p => p.1 + 1)
    Primrec.id (Primrec.const 0)
    (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)).to₂).of_eq
      fun xs => by cases xs <;> rfl

theorem execSparse_primrec (q : NumericStmt) :
    Primrec (execSparse q) := by
  induction q with
  | push k table next ih =>
      have hstack : Primrec fun c : SparseNumericState =>
          sparseStackLookup c.stackData k :=
        sparseStackLookup_primrec₂.comp sparseNumericState_stackData_primrec
          (Primrec.const k)
      have hvalue : Primrec fun c : SparseNumericState =>
          table.getD c.state 0 :=
        (Primrec.list_getD 0).comp (Primrec.const table)
          sparseNumericState_state_primrec
      have hxs : Primrec fun c : SparseNumericState =>
          table.getD c.state 0 :: sparseStackLookup c.stackData k :=
        Primrec.list_cons.comp hvalue hstack
      have hstacks : Primrec fun c : SparseNumericState =>
          sparseStackUpdate c.stackData k
            (table.getD c.state 0 :: sparseStackLookup c.stackData k) :=
        sparseStackUpdate_primrec.comp
          (Primrec.pair sparseNumericState_stackData_primrec
            (Primrec.pair (Primrec.const k) hxs))
      exact ih.comp (sparseNumericState_mk_primrec
        sparseNumericState_label_primrec sparseNumericState_state_primrec hstacks)
  | peek k width table next ih =>
      have hstack : Primrec fun c : SparseNumericState =>
          sparseStackLookup c.stackData k :=
        sparseStackLookup_primrec₂.comp sparseNumericState_stackData_primrec
          (Primrec.const k)
      have hi : Primrec fun c : SparseNumericState =>
          c.state * width + headCode (sparseStackLookup c.stackData k) :=
        Primrec.nat_add.comp
          (Primrec.nat_mul.comp sparseNumericState_state_primrec
            (Primrec.const width))
          (headCode_primrec.comp hstack)
      have hstate : Primrec fun c : SparseNumericState =>
          table.getD
            (c.state * width + headCode (sparseStackLookup c.stackData k)) 0 :=
        (Primrec.list_getD 0).comp (Primrec.const table) hi
      exact ih.comp (sparseNumericState_mk_primrec
        sparseNumericState_label_primrec hstate
        sparseNumericState_stackData_primrec)
  | pop k width table next ih =>
      have hstack : Primrec fun c : SparseNumericState =>
          sparseStackLookup c.stackData k :=
        sparseStackLookup_primrec₂.comp sparseNumericState_stackData_primrec
          (Primrec.const k)
      have hi : Primrec fun c : SparseNumericState =>
          c.state * width + headCode (sparseStackLookup c.stackData k) :=
        Primrec.nat_add.comp
          (Primrec.nat_mul.comp sparseNumericState_state_primrec
            (Primrec.const width))
          (headCode_primrec.comp hstack)
      have hstate : Primrec fun c : SparseNumericState =>
          table.getD
            (c.state * width + headCode (sparseStackLookup c.stackData k)) 0 :=
        (Primrec.list_getD 0).comp (Primrec.const table) hi
      have hstacks : Primrec fun c : SparseNumericState =>
          sparseStackUpdate c.stackData k
            (sparseStackLookup c.stackData k).tail :=
        sparseStackUpdate_primrec.comp
          (Primrec.pair sparseNumericState_stackData_primrec
            (Primrec.pair (Primrec.const k)
              (Primrec.list_tail.comp hstack)))
      exact ih.comp (sparseNumericState_mk_primrec
        sparseNumericState_label_primrec hstate hstacks)
  | load table next ih =>
      have hstate : Primrec fun c : SparseNumericState =>
          table.getD c.state 0 :=
        (Primrec.list_getD 0).comp (Primrec.const table)
          sparseNumericState_state_primrec
      exact ih.comp (sparseNumericState_mk_primrec
        sparseNumericState_label_primrec hstate
        sparseNumericState_stackData_primrec)
  | branch table yes no ihYes ihNo =>
      have hvalue : Primrec fun c : SparseNumericState =>
          table.getD c.state 0 :=
        (Primrec.list_getD 0).comp (Primrec.const table)
          sparseNumericState_state_primrec
      exact Primrec.ite
        (Primrec.eq.comp hvalue (Primrec.const 0)) ihNo ihYes
  | goto table =>
      have hstate : Primrec fun c : SparseNumericState =>
          table.getD c.state 0 :=
        (Primrec.list_getD 0).comp (Primrec.const table)
          sparseNumericState_state_primrec
      exact sparseNumericState_mk_primrec
        (Primrec.option_some.comp hstate)
        sparseNumericState_state_primrec sparseNumericState_stackData_primrec
  | halt =>
      exact sparseNumericState_mk_primrec (Primrec.const none)
        sparseNumericState_state_primrec sparseNumericState_stackData_primrec

noncomputable def numericProgram (tm : FinTM2) : List NumericStmt := by
  letI := tm.ΛFin
  exact List.ofFn fun i : Fin (Fintype.card tm.Λ) =>
    let l := (Fintype.equivFin tm.Λ).symm i
    numericStmt tm (tm.m l) (FinTM2.generatedBy_main_available tm l)

theorem numericProgram_getElem? (tm : FinTM2) (pc : ℕ) :
    (numericProgram tm)[pc]? =
      match @finDecode tm.Λ tm.ΛFin pc with
      | none => none
      | some l => some
          (numericStmt tm (tm.m l) (FinTM2.generatedBy_main_available tm l)) := by
  letI := tm.ΛFin
  unfold numericProgram
  rw [List.getElem?_ofFn]
  unfold finDecode
  split <;> rfl

/-- Execute the statement at a numeric program counter. -/
def sparseNumericExecAt (p : List NumericStmt) (pc : ℕ)
    (c : SparseNumericState) : Option SparseNumericState :=
  p[pc]?.map fun q => execSparse q c

theorem sparseNumericExecAt_primrec (p : List NumericStmt) :
    Primrec fun q : ℕ × SparseNumericState =>
      sparseNumericExecAt p q.1 q.2 := by
  induction p with
  | nil => exact Primrec.const none
  | cons stmt p ih =>
      have hpc : Primrec fun q : ℕ × SparseNumericState => q.1 := Primrec.fst
      have hzero : Primrec fun q : ℕ × SparseNumericState =>
          some (execSparse stmt q.2) :=
        Primrec.option_some.comp
          ((execSparse_primrec stmt).comp Primrec.snd)
      have hsucc : Primrec₂ fun (q : ℕ × SparseNumericState) (pc : ℕ) =>
          sparseNumericExecAt p pc q.2 := by
        change Primrec fun z : (ℕ × SparseNumericState) × ℕ =>
          sparseNumericExecAt p z.2 z.1.2
        exact ih.comp (Primrec.pair Primrec.snd
          (Primrec.snd.comp Primrec.fst))
      exact (Primrec.nat_casesOn hpc hzero hsucc).of_eq fun q => by
        cases q.1 <;> rfl

noncomputable def sparseNumericStep (tm : FinTM2)
    (c : SparseNumericState) : Option SparseNumericState :=
  match c.label with
  | none => none
  | some pc => sparseNumericExecAt (numericProgram tm) pc c

theorem sparseNumericStep_primrec (tm : FinTM2) :
    Primrec (sparseNumericStep tm) := by
  have hnext : Primrec₂ fun (c : SparseNumericState) (pc : ℕ) =>
      sparseNumericExecAt (numericProgram tm) pc c := by
    change Primrec fun q : SparseNumericState × ℕ =>
      sparseNumericExecAt (numericProgram tm) q.2 q.1
    exact (sparseNumericExecAt_primrec (numericProgram tm)).comp
      (Primrec.pair Primrec.snd Primrec.fst)
  exact (Primrec.option_bind sparseNumericState_label_primrec hnext).of_eq
    fun c => by unfold sparseNumericStep; cases c.label <;> rfl

theorem sparseNumericStep_toNumeric (tm : FinTM2)
    (c : SparseNumericState) :
    Option.map SparseNumericState.toNumeric (sparseNumericStep tm c) =
      FinTM2.numericStep tm c.toNumeric := by
  unfold sparseNumericStep FinTM2.numericStep
  cases hc : c.label with
  | none => simp [SparseNumericState.toNumeric, hc]
  | some pc =>
      simp only [hc, SparseNumericState.toNumeric]
      unfold sparseNumericExecAt
      rw [numericProgram_getElem?]
      cases hd : @finDecode tm.Λ tm.ΛFin pc with
      | none => rfl
      | some l =>
          simp only [hd, Option.map_some]
          rw [execSparse_toNumeric]
          have hcnum : c.toNumeric =
              ({ label := some pc
                 state := c.state
                 stackData := sparseStackLookup c.stackData } :
                NumericMachineState) := by
            apply NumericMachineState.ext
            · simpa [SparseNumericState.toNumeric] using hc
            · rfl
            · rfl
          rw [hcnum]

noncomputable def sparseNumericStepOption (tm : FinTM2) :
    Option SparseNumericState → Option SparseNumericState :=
  fun oc => oc.bind (sparseNumericStep tm)

noncomputable def numericStepOption (tm : FinTM2) :
    Option NumericMachineState → Option NumericMachineState :=
  fun oc => oc.bind (FinTM2.numericStep tm)

theorem sparseNumericStepOption_primrec (tm : FinTM2) :
    Primrec (sparseNumericStepOption tm) :=
  Primrec.option_bind₁ (sparseNumericStep_primrec tm)

theorem sparseNumericStepOption_toNumeric (tm : FinTM2)
    (oc : Option SparseNumericState) :
    Option.map SparseNumericState.toNumeric (sparseNumericStepOption tm oc) =
      numericStepOption tm (Option.map SparseNumericState.toNumeric oc) := by
  cases oc with
  | none => rfl
  | some c => exact sparseNumericStep_toNumeric tm c

noncomputable def sparseNumericIter (tm : FinTM2) (t : ℕ)
    (c : SparseNumericState) : Option SparseNumericState :=
  ((sparseNumericStepOption tm)^[t]) (some c)

theorem sparseNumericIter_primrec (tm : FinTM2) :
    Primrec fun q : ℕ × SparseNumericState =>
      sparseNumericIter tm q.1 q.2 := by
  have hstart : Primrec fun _q : ℕ × SparseNumericState =>
      some _q.2 := Primrec.option_some.comp Primrec.snd
  have hstep : Primrec₂ fun (_q : ℕ × SparseNumericState)
      (oc : Option SparseNumericState) => sparseNumericStepOption tm oc :=
    ((sparseNumericStepOption_primrec tm).comp Primrec.snd).to₂
  exact Primrec.nat_iterate Primrec.fst hstart hstep

theorem sparseNumericIter_toNumeric_option (tm : FinTM2)
    (t : ℕ) (oc : Option SparseNumericState) :
    Option.map SparseNumericState.toNumeric
        (((sparseNumericStepOption tm)^[t]) oc) =
      ((numericStepOption tm)^[t])
        (Option.map SparseNumericState.toNumeric oc) := by
  induction t generalizing oc with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      rw [sparseNumericStepOption_toNumeric]

theorem sparseNumericIter_toNumeric (tm : FinTM2)
    (t : ℕ) (c : SparseNumericState) :
    Option.map SparseNumericState.toNumeric (sparseNumericIter tm t c) =
      ((numericStepOption tm)^[t]) (some c.toNumeric) := by
  exact sparseNumericIter_toNumeric_option tm t (some c)

end Lax51Proofs.Computability
