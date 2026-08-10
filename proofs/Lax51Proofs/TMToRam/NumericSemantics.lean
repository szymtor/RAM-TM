import Lax51Proofs.TMToRam.NumericStmt

/-!
Executable semantics of the normalized numeric statement tree. It mirrors
`TM2.stepAux`, but all finite control and stack symbols are naturals and all
control functions are literal tables.
-/

namespace Lax51Proofs.TMToRam

open Turing

/-- A fully numeric machine configuration. Stack indices are finite-control
codes; indices outside the machine's stack type remain empty. -/
structure NumericMachineState where
  label : Option ℕ
  state : ℕ
  stackData : ℕ → List ℕ

@[ext] theorem NumericMachineState.ext (c d : NumericMachineState)
    (hlabel : c.label = d.label) (hstate : c.state = d.state)
    (hstacks : c.stackData = d.stackData) : c = d := by
  cases c
  cases d
  simp_all

/-- Code `none` as zero and a present head code as one plus that code. -/
def headCode : List ℕ → ℕ
  | [] => 0
  | a :: _ => a + 1

/-- Encode a dependent family of typed stacks as a total family of numeric
stacks. Invalid numeric stack indices denote the empty stack. -/
noncomputable def FinTM2.codeStackFamily (tm : FinTM2)
    (S : ∀ k, List (tm.Γ k))
    (hS : StacksWithin (FinTM2.availableSymbols tm) S) : ℕ → List ℕ := by
  letI := tm.kFin
  exact fun i =>
    match finDecode tm.K i with
    | none => []
    | some k => FinTM2.codeStack tm k (S k) (fun a ha => hS k a ha)

theorem FinTM2.codeStackFamily_update (tm : FinTM2)
    (S : ∀ k, List (tm.Γ k)) (hS : StacksWithin (FinTM2.availableSymbols tm) S)
    (k : tm.K) (xs : List (tm.Γ k))
    (hxs : ∀ a ∈ xs, (⟨k, a⟩ : Σ k, tm.Γ k) ∈ FinTM2.availableSymbols tm)
    (hS' : StacksWithin (FinTM2.availableSymbols tm) (Function.update S k xs)) :
    Function.update (codeStackFamily tm S hS)
        (@finCode tm.K tm.kFin tm.kDecidableEq k) (codeStack tm k xs hxs) =
      codeStackFamily tm (Function.update S k xs) hS' := by
  letI := tm.kFin
  letI : DecidableEq tm.K := tm.kDecidableEq
  funext i
  by_cases hi : i = finCode k
  · subst i
    rw [Function.update_self]
    simp [codeStackFamily]
  · rw [Function.update_of_ne hi]
    unfold codeStackFamily
    split <;> rename_i hdec
    · rfl
    · rename_i j
      have hji : finCode j = i := finCode_of_finDecode_eq_some hdec
      have hjk : j ≠ k := by
        intro hjk
        subst j
        exact hi hji.symm
      simp only [Function.update_of_ne hjk]

theorem FinTM2.headCode_codeStack (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k))
    (hxs : ∀ a ∈ xs, (⟨k, a⟩ : Σ k, tm.Γ k) ∈ availableSymbols tm) :
    headCode (codeStack tm k xs hxs) =
      headOptionCode tm k (availableHeadOption tm k xs hxs) := by
  cases xs with
  | nil => simp [headCode, headOptionCode, availableHeadOption, optionCode]
  | cons a xs =>
      simp [headCode, headOptionCode, availableHeadOption, optionCode, codeSymbol]

/-- Encode a typed Turing configuration as a fully numeric configuration.
The stack family is addressed by finite enumeration codes. -/
noncomputable def FinTM2.encodeNumericState (tm : FinTM2) (c : tm.Cfg)
    (hc : StacksWithin (FinTM2.availableSymbols tm) c.stk) : NumericMachineState := by
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : DecidableEq tm.Λ := Classical.decEq _
  letI : DecidableEq tm.σ := Classical.decEq _
  exact {
    label := c.l.map finCode
    state := finCode c.var
    stackData := FinTM2.codeStackFamily tm c.stk hc
  }

@[simp] theorem FinTM2.encodeNumericState_stack (tm : FinTM2) (c : tm.Cfg)
    (hc : StacksWithin (FinTM2.availableSymbols tm) c.stk) (k : tm.K) :
    (FinTM2.encodeNumericState tm c hc).stackData
      (@finCode tm.K tm.kFin tm.kDecidableEq k) =
      FinTM2.codeStack tm k (c.stk k) (fun a ha => hc k a ha) := by
  letI := tm.kFin
  letI : DecidableEq tm.K := tm.kDecidableEq
  simp [FinTM2.encodeNumericState, FinTM2.codeStackFamily]

/-- Execute a normalized statement tree atomically. -/
def NumericStmt.exec : NumericStmt → NumericMachineState → NumericMachineState
  | .push k table next, c =>
      let S := Function.update c.stackData k (table.getD c.state 0 :: (c.stackData k))
      next.exec { c with stackData := S }
  | .peek k width table next, c =>
      let i := c.state * width + headCode (c.stackData k)
      next.exec { c with state := table.getD i 0 }
  | .pop k width table next, c =>
      let i := c.state * width + headCode (c.stackData k)
      let S := Function.update c.stackData k ((c.stackData k).tail)
      let c' := { c with state := table.getD i 0 }
      next.exec { c' with stackData := S }
  | .load table next, c => next.exec { c with state := table.getD c.state 0 }
  | .branch table yes no, c =>
      if table.getD c.state 0 = 0 then no.exec c else yes.exec c
  | .goto table, c => { c with label := some (table.getD c.state 0) }
  | .halt, c => { c with label := none }

theorem numericStmt_exec_goto (tm : FinTM2) (f : tm.σ → tm.Λ)
    (l : Option tm.Λ) (s : tm.σ) (S : ∀ k, List (tm.Γ k))
    (hS : StacksWithin (FinTM2.availableSymbols tm) S)
    (hgen : ∀ z, SigmaGeneratedBy (.goto f : TM2.Stmt tm.Γ tm.Λ tm.σ) z →
      z ∈ FinTM2.availableSymbols tm) :
    (numericStmt tm (.goto f) hgen).exec
        (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS) =
      FinTM2.encodeNumericState tm (TM2.stepAux (.goto f) s S)
        (stepAux_stacksWithin _ _ _ _ hS hgen) := by
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : DecidableEq tm.Λ := Classical.decEq _
  letI : DecidableEq tm.σ := Classical.decEq _
  simp only [numericStmt, NumericStmt.exec]
  rw [show (unaryTable f).getD
      (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS).state 0 = finCode (f s) by
    simpa [FinTM2.encodeNumericState] using unaryTable_getD f s 0]
  ext <;> simp [FinTM2.encodeNumericState]

theorem numericStmt_exec_halt (tm : FinTM2)
    (l : Option tm.Λ) (s : tm.σ) (S : ∀ k, List (tm.Γ k))
    (hS : StacksWithin (FinTM2.availableSymbols tm) S)
    (hgen : ∀ z, SigmaGeneratedBy (.halt : TM2.Stmt tm.Γ tm.Λ tm.σ) z →
      z ∈ FinTM2.availableSymbols tm) :
    (numericStmt tm .halt hgen).exec
        (FinTM2.encodeNumericState tm ⟨l, s, S⟩ hS) =
      FinTM2.encodeNumericState tm (TM2.stepAux .halt s S)
        (stepAux_stacksWithin _ _ _ _ hS hgen) := by
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : DecidableEq tm.Λ := Classical.decEq _
  letI : DecidableEq tm.σ := Classical.decEq _
  ext <;> simp [numericStmt, NumericStmt.exec, FinTM2.encodeNumericState]

end Lax51Proofs.TMToRam
